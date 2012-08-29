{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses, NoMonomorphismRestriction,
    FlexibleContexts, FlexibleInstances #-}
-----------------------------------------------------------------------------
{-|
 Module      :  GM
 Copyright   :  2011 Christian Gosch
 License     :  AllRightsReserved

 Maintainer  : Christian Gosch
 Stability   : Experimental
 Portability : GHC 7
 
This is intended to be a module for graphical model algorithms.

So far, maxSum and sumProduct work on trees only. Support for other message passing schemes
may be added in the future.
The implementation may be a little inefficient at some places, and also may contain code which
can be written in a much more beautiful way.
Specifically, the helper functions backtrack' and backtrack are worth a mention
and may be implemented differently in the future.
It is definitely work in progress, but it seems to work.
If it does not, please let me (the author) know!
-}
--
-----------------------------------------------------------------------------

module GM 
       (
         -- * Algorithms
         maxSum,
         sumProduct,
         -- * Data structures
         FactorGraph(..),
         MessageMap,
         NodeMap,
         Node(..),
         Message(..),
         -- * Factor graph monad --- running the algorithms
         -- FGMClass(..),
         FGMDebug,
         runFGMDebugLog,
         FGM,
         runFGM,
         -- * FGMClass convenience functions
         getGraph,
         getNodes,
         getMessages,
         marginal,
         normalisationConstant,
         -- * Test graphs
         testGraph,
         testGraph2
         )
       where

import qualified Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.DFS (dfs, udfs)
import Data.Graph.Inductive.Query.BFS (bfs)
import Data.Tuple (swap)
import Data.Maybe (catMaybes, isNothing, fromJust, isJust)
import Data.List (partition, sort, elemIndex, nub, foldl1', (!!))
import Data.Array
import Data.Foldable (foldl')
import Data.Ix
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Control.Parallel.Strategies
import Control.Parallel

--import Debug.Trace
trace :: String -> a -> a
trace _ a = a

class (Num b) => Integrate a b where
    integrate :: a -> a -> (a -> b) -> b  -- bounds, function, result

instance Num a => Integrate Int a where
    integrate a b f = sum $ map f [a..b]

instance (Ix a, Integral a, Integrate a b) => Integrate [a] b where
    integrate as bs f = sum $ map f p
        where p = allCombinations $ zip as bs

-- Integer variant
class (Integrate a b, Ix a, Integral a) => IIntegrate a b
instance IIntegrate Int Float
instance IIntegrate Int Double

-- Finding maxima and minima over functions
class (Ord b) => Boundsf a b where
    argmax, argmin :: (a,a) -> (a -> b) -> a


instance (Ord b, Ix a) => Boundsf [a] b where
    argmax (s,e) f = maximum' p f
        where p = allCombinations $ zip s e
    argmin (s,e) f = minimum' p f
        where p = allCombinations $ zip s e

maximum', minimum' :: Ord b => [a] -> (a -> b) -> a
minmaxf :: Ord b => (a -> b) -> a -> a -> (a,a)
minmaxf f x y | f x < f y = (x,y)
              | otherwise = (y,x)
maximum' xs@(x1:_) f = foldl' (\x y -> if (f x) < (f y) then y else x) x1 xs
minimum' xs@(x1:_) f = foldl' (\x y -> if (f x) >= (f y) then y else x) x1 xs


{-| Generate all combinations of integers with the given ranges for each position.
NOTE: This took about 28 clock ticks per generated combination on 1 core on an AMD Phenom,
compiled with ghc -O and used only to output the length of the list. Measured with 3-element lists. -}
allCombinations :: Ix a => [(a,a)] -> [[a]]
allCombinations (r:[]) = map (:[]) (range r)
allCombinations (r:rs) = concatMap (rest' r) rest
  where
    -- rest' :: Range -> [Int] -> [[Int]]
    rest' r other_digits = map (:other_digits) (range r)
      -- withStrategy (parList rseq) $ map (:other_digits) rr
    -- rr = range r
    rest = allCombinations rs
allCombinations [] = undefined
{-# SPECIALIZE allCombinations :: [(Int,Int)] -> [[Int]] #-}


-- data Integrate a b => Node a b = Variable a | Factor ([a] -> b) -- Achtung, Reihenfolge der [a]!

-- Daten auf den Labels direkt scheint keine gute Idee zu sein. Setzt bestimmte Klassenzugehoerig-
-- keiten voraus (zB Eq). Ich nehme an, dafuer sind die labels nicht gedacht.
-- Die Daten (Variable, Faktoren, Nachrichten) sollten daher extern gespeichert werden,
-- zB in einer Liste oder einer Map oder einer IntMap (schnelle map von Int auf a).

data FactorGraph gr a b = FactorGraph { fgGraph :: gr () (), 
                                        fgMessages :: MessageMap a b, 
                                        fgNodes :: NodeMap a b }

-- Extra information for nodes: Variables and Factors
data Node a b = Variable { varValue :: Maybe a, -- ^ varValue is not really used yet. It may be used to clamp variables in the future.
                           varBounds :: (a,a)   -- ^ The bounds of the variable (interval of valid values).
                         }
              | Factor ([a] -> b) -- ^ The factor function, taking values of the (ascending sorted) neighbour variable nodes as parameter.

-- Messages for the edges.
data Message a b = Message (a -> b) -- ^ The message function.
                 | MaxSumFactorMessage (a -> b) (a -> [a]) -- ^ For max-sum, special factor messages are used to store the optimal variable values for back-tracking. These messages are used in max-sum from factor nodes to variable nodes.
messageFunction (Message f) = f
messageFunction (MaxSumFactorMessage f _) = f

instance Show (Node a b) where
    show (Variable _ _) = "var"
    show (Factor _) = "fac"

instance Show (Message a b) where
    show _ = "msg"

type MessageMap a b = M.Map G.Edge (Message a b)
type NodeMap a b = IM.IntMap (Node a b)


  


-- newtype (G.DynGraph gr) => FactorGraph gr = FactorGraph { fgGraph :: gr () () }

data FGState gr a b =
  FGState { fgsFG :: FactorGraph gr a b }

isVariable :: Node a b -> Bool
isVariable (Variable _ _) = True
isVariable _ = False

isFactor = not . isVariable

emptyFGState :: (G.DynGraph gr, Integrate a b) => FactorGraph gr a b -> FGState gr a b
emptyFGState gr = FGState gr
-- NOTE: Fuer den Graph muessen die Variable und Faktoren angegeben werden.

-- Factor graph monad
class FGMClass m where
    runFGM :: (Integrate a b, G.DynGraph gr) => FactorGraph gr a b -> m gr a b c -> c
    dbgMsg :: String -> m gr a b ()
    getFGState :: m gr a b (FGState gr a b)
    modifyFGState :: (FGState gr a b -> FGState gr a b) -> m gr a b ()


newtype FGM gr a b c = FGM { unFGM :: StateT (FGState gr a b) Identity c} deriving Monad
newtype FGMDebug gr a b c = FGMDebug { unFGMDebug :: StateT (FGState gr a b) (Writer [String]) c} deriving Monad

instance FGMClass FGM where
    runFGM = runFGM'
    dbgMsg _ = return ()
    getFGState = FGM $ get
    modifyFGState = FGM . modify

instance FGMClass FGMDebug where
    runFGM = runFGMDebug
    dbgMsg s = FGMDebug $ lift $ tell [s]
    getFGState = FGMDebug $ get
    modifyFGState = FGMDebug . modify


runFGM' :: (Integrate a b, G.DynGraph gr) => FactorGraph gr a b -> FGM gr a b c -> c
runFGM' fg f = runIdentity $ evalStateT (unFGM f) (FGState fg)

runFGMDebug :: (Integrate a b, G.DynGraph gr) => FactorGraph gr a b -> FGMDebug gr a b c -> c
runFGMDebug fg f = fst $ runFGMDebugLog fg f

runFGMDebugLog :: (Integrate a b, G.DynGraph gr) => FactorGraph gr a b -> FGMDebug gr a b c -> (c,[String])
runFGMDebugLog fg f = runWriter $ evalStateT (unFGMDebug f) (FGState fg)


--getFG :: (FGMClass m a b, G.DynGraph gr, Integrate a b) => m gr a b (FactorGraph gr)
--getFG = return $ fmap fgsFG get

getMessages :: (Monad (m gr a b), FGMClass m) => m gr a b (MessageMap a b)
getMessages = getFGState >>= return . fgMessages . fgsFG

getNodes :: (Monad (m gr a b), FGMClass m) => m gr a b (NodeMap a b)
getNodes = getFGState >>= return . fgNodes . fgsFG

getGraph :: (Monad (m gr a b), FGMClass m) => m gr a b (gr () ())
getGraph = getFGState >>= return . fgGraph . fgsFG

{-| Returns a list of all incoming messages. Messages which are not present are /Nothing/.
    The messages are sorted in ascending order of node numbers. -}
incomingMessages :: (Monad (m gr a b), FGMClass m, G.Graph gr) => G.Node -> m gr a b [Maybe (Message a b)]
incomingMessages n = do
  mm <- getMessages
  gr <- getGraph
  let neigh = sort $ G.pre gr n
      mincoming = map (\i -> M.lookup (i,n) mm) neigh
  return mincoming


{-| Returns the neighbour nodes, sorted, of a given node. -}
neighbours :: (Monad (m gr a b), FGMClass m, G.Graph gr) => G.Node -> m gr a b [G.Node]
neighbours n = getGraph >>= return . sort . nub . ((flip G.neighbors) n)


{-| Compute the /unnormalised/ marginal at the specified variable node. Get the normalisation factor with normalisationConstant. -}
marginal :: (Monad (m gr a b), FGMClass m, Num b, G.DynGraph gr, Integrate a b) => G.Node -> m gr a b (a -> b)
marginal n = do
  nodes <- getNodes
  let mnode = IM.lookup n nodes
  case mnode of
    Just (Variable mval bds) -> do
      mincoming <- incomingMessages n
      dbgMsg $ "Computing marginal using incoming messages on node " ++ show n ++ ", " ++ show mincoming
      let incoming_prod = sequence mincoming >>= return . prod'messages
      case incoming_prod of
        Nothing -> error "marginal: An incoming message was not present!"
        Just f -> dbgMsg "Returning the marginal." >> return f
    Just (Factor _) -> error $ "Call factorMarginal for factor nodes. Node " ++ show n ++ " is a factor node."


{-| Computes the product of all messages for a given value. -}
prod'messages :: Num b => [Message a b] -> a -> b
prod'messages [] _ = 1
prod'messages (Message f : msgs) a = fa * prod'messages msgs a
  where fa = f a


{-| Compute the /unnormalised/ marginal for a factor node. 
THIS IS UNTESTED! -}
factorMarginal :: (Monad (m gr a b), FGMClass m, Num b, G.DynGraph gr, Integrate a b) => 
                 G.Node                                   -- ^ Node to compute the marginal for (must be a factor node).
                 -> m gr a b ([(a,a)], [G.Node], [a] -> b)  -- ^ A triple: the bounds of the neighbouring variables, the (sorted) neighbouring variable nodes, and the marginal.
factorMarginal n = do
  nodes <- getNodes
  let mnode = IM.lookup n nodes
  case mnode of
    Just (Factor f) -> do
      mincoming <- incomingMessages n
      if any isNothing mincoming 
        then error ("factorMarginal " ++ show n ++ ": an incoming message is invalid.")
        else return ()
      let incoming = catMaybes mincoming
      let marg xs = f xs * (product $ map (\(Message f',x) -> f' x) $ zip incoming xs)
      neigh <- neighbours n
      let mbds = sequence $ map (\i -> IM.lookup i nodes >>= \(Variable mval b) -> return b) neigh
      case mbds of
        Just bds -> return (bds, neigh, marg)
        _ -> error $ "factorMarginal " ++ show n ++ ": something went wrong."
        

{-| Compute the normalisation constant 1\/Z, by marginalising over node variable node /n/ (any will do). -}
normalisationConstant :: (Fractional b, Monad (m gr a b), FGMClass m, G.DynGraph gr, Integrate a b) => G.Node -> m gr a b b
normalisationConstant n = do
  m <- marginal n
  nodes <- getNodes
  let mnode = IM.lookup n nodes
  case mnode of 
    Just (Variable mval (a,b)) -> return $ recip $ integrate a b m
    _ -> error $ "normalisationConstant: node " ++ show n ++ " does not exist or is not a variable."




insertIfNotExist k v m = if M.notMember k m then M.insert k v m else m


{-| Runs the sum-product algorithm on the given current graph. -}
sumProduct :: (Monad (m gr a b), FGMClass m, Num b, G.DynGraph gr, IIntegrate a b) => m gr a b ()
sumProduct = do
    gr <- getGraph
    mm <- getMessages
    nm <- getNodes
    let (vnodes, fnodes) = partition (isVariable . snd) $ IM.toList nm
    -- Eigentlich sollte man mit DFS bei den _untersten_ Knoten anfangen (Blaetter)
    -- und dann sich nach oben arbeiten. Die Reihenfolge der Knoten von dfs/udfs ist allerdings
    -- von der Wurzel beginnend. Daher habe ich die Reihenfolge von DFS umgedreht.
    -- Muesste stimmen, solange es sich um einen Baum handelt!
    let dfsnodes = reverse $ udfs [fst $ head vnodes] gr
    let bfsnodes = bfs (fst (head vnodes)) gr
    mapM_ processNode dfsnodes -- Pass 1: From the leaves to the root
    mapM_ processNode bfsnodes -- Pass 2: From the root back to the leaves
    dbgMsg $ "Node order dfs: " ++ show dfsnodes
    dbgMsg $ "Node order bfs: " ++ show bfsnodes
    mm <- getMessages
    dbgMsg $ "Message map: " ++ show mm
        where
            processNode :: (Monad (m gr a b), FGMClass m, IIntegrate a b, G.DynGraph gr) => G.Node -> m gr a b ()
            processNode n = do
                gr <- getGraph
                mm <- getMessages
                nm <- getNodes
                let neigh = nub $ G.neighbors gr n
                let mnode = IM.lookup n nm
                case mnode of
                    Just (Variable mv bds) -> do
                        updateMessages $! map (variableMessage product n neigh mm) neigh
                    Just (Factor f) -> do
                        updateMessages $! map (factorMessage f n neigh mm nm) neigh
                        
                        dbgMsg $ "Factor " ++ show n
                        dbgMsg $ "n = " ++ show n ++ ", neigh = " ++ show neigh ++ ", lookup: " ++
                            show (map (\x -> M.lookup (x,n) mm) neigh) ++
                            ", mmessages: " ++ show (map (factorMessage f n neigh mm nm) neigh)
                    _ -> return ()


{-| Update the message map with those given messages which are not /Nothing/. -}
updateMessages :: (Monad (m gr a b), FGMClass m) => [Maybe (G.Edge, Message a b)] -> m gr a b ()
updateMessages mmessages = do
  mm <- getMessages
  let mnewmap = sequence (filter isJust mmessages) >>= \messages ->
        return (foldl' (\m (k,v) -> M.insert k v m) mm messages)
        --return (foldl' (\m (k,v) -> insertIfNotExist k v m) mm messages)
  case mnewmap of
    Just m -> do
      mapM_ f (filter isJust mmessages)
      modifyFGState $! \s -> s { fgsFG = (fgsFG s) { fgMessages = m} }
        where f (Just ((a,b),_)) = return () -- Just add the message
              f _                = dbgMsg $ "OH DEAR! mmessages still contains a Nothing." -- Error!
    _ -> return ()



{-| Given a factor function f_s with it's node number n_f, all neighbouring nodes, message and node maps, and
    the node n_n to compute the message to, returns the edge (n_f,n_n) with the message \mu_{f_s -> x}(x) or Nothing. -}
factorMessage :: (Ix a, Integral a, Num b, IIntegrate a b) =>
    ([a] -> b)         -- ^ Factor function, f_s
    -> G.Node          -- ^ This factor node
    -> [G.Node]        -- ^ /All/ neighbouring nodes
    -> MessageMap a b  -- ^ The message map
    -> NodeMap a b     -- ^ The node map
    -> G.Node          -- ^ The node to compute the message to
    -> Maybe (G.Edge, Message a b)
factorMessage f n neigh mm nm o = mf'
  where neigh'' = sort neigh
        mn = elemIndex o neigh''
        mbds = map getBds neigh''
        -- Incoming messages from neighbouring variable nodes, here including o
        mincoming = map f neigh''
            where f x | x /= o = M.lookup (x,n) mm
                      | otherwise = Just $! Message (const 1)
        getBds node = 
          IM.lookup node nm >>= \v ->
          if isVariable v
          then return $ varBounds v
          else error $ "Error in the graph structure -- node " ++ show v ++ " is a factor node and is connected to a factor node."
                       -- This was a factor node -- should not happen,
                       -- that indicates an error in the graph structure.
        mf' = do
            incoming <- sequence mincoming
            bds <- sequence mbds
            n' <- mn
            let table = factorTable (n,o) f bds incoming n' 
                        -- If we move the let into the Message below, the interpreter
                        -- apparently computes the table anew at each call to the Message. Doing it this way ensures that
                        -- the table is computed only once and referenced afterwards.
            return ((n,o), Message (\a -> table ! a))


{-| For a given factor node function from the factor node to a variable node, 
    computes a table containing the value of the factor message function \mu_{f_s -> c}(x) for 
    every value of x. 
    See the equation (8.66) in Bishop, that's what is computed here. -}
factorTable :: (Num a, Ix a, IIntegrate a b) => (G.Node, G.Node) -- Just for debugging
    -> ([a] -> b)      -- ^ Function /f/ to compute the integral or sum over (the factor node's function).
    -> [(a,a)]        -- ^ Bounds (inclusive) for /all/ the incoming functions (messages). Sums are computed for these values, must be the same length as the list the function /f/ expects as its first argument.
    -> [Message a b]  -- ^ All the incoming messages into the node we are computing on (which is a factor node).
    -> Int            -- ^ The index /n/ of the argument to /f/ that will be used as index into the returned table.
    -> Array a b      -- ^ Contains the value of sum_(x_1,.,x_n,..,x_N) f(x_1,..,x_n,..,x_N) * prod(incoming\\incoming_n) for each value of the /n/'th variable of /f/.
factorTable (source,target) f bds incoming n = table -- trace ("from " ++ show source ++ " to " ++ show target) table 
  where
    table = array nbds tableList
      where tableList = [(a, int'f $! a) | a <- range nbds]
            -- Experimenting with parallel execution a little bit. So far no big success.
            tableListP = parMap rpar (\a -> let ifa = int'f a in (a, ifa)) (range nbds)
            
            -- tableListP = runEval $ parListChunk 20 (evalTuple2 r0 rseq) $ map (\a -> let ifa = int'f a in ifa `pseq` (a, ifa)) (range nbds)
    nbds = bds !! n
    sz = rangeSize nbds
    -- int'f x computes \mu_{f_s -> x}(x), Bishop eqn. (8.66).
    int'f a = integrate as bs $! (f'factor 1 (*) f incoming')
      where as = replace n a $! map fst bds 
            bs = replace n a $! map snd bds

    -- Replace the message coming from the node n for which we are computing the factor message,
    -- with the constant function returning 1.
    incoming' = replace n (Message $! const 1) incoming

            
            
            
{-| Used for backtracking. See the notes for /backtracking'/ in the source code. -}
data BacktrackMessage a = BTM G.Edge a deriving Show

{-| Runs the max-sum algorithm on the current graph. Returns an association list of nodes to optimal variable values. -}
maxSum :: (Show a, Monad (m gr a b), Floating b, Ord b, FGMClass m, Num b, G.DynGraph gr, IIntegrate a b) => m gr a b [(G.Node, a)]
maxSum = do
    gr <- getGraph
    mm <- getMessages
    nm <- getNodes
    let (vnodes, fnodes) = partition (isVariable . snd) $ IM.toList nm
    -- Eigentlich sollte man mit DFS bei den _untersten_ Knoten anfangen (Blaetter)
    -- und dann sich nach oben arbeiten. Die Reihenfolge der Knoten von dfs/udfs ist allerdings
    -- von der Wurzel beginnend. Daher habe ich die Reihenfolge von DFS umgedreht.
    -- Muesste stimmen, solange es sich um einen Baum handelt!
    let startNode = fst $ head vnodes
    let dfsnodes = reverse $ udfs [startNode] gr
    let bfsnodes = bfs (startNode) gr
    mapM_ processNode dfsnodes -- Pass 1: From the leaves to the root
    varValues <- backtrack' startNode -- Pass 2: Backtracking.
    dbgMsg $ "varValues: " ++ show varValues
    dbgMsg $ "Node order dfs: " ++ show dfsnodes
    dbgMsg $ "Node order bfs: " ++ show bfsnodes
    mm <- getMessages
    dbgMsg $ "Message map: " ++ show mm
    return varValues
        where
            processNode :: (Monad (m gr a b), Floating b, Ord b, FGMClass m, IIntegrate a b, G.DynGraph gr) => G.Node -> m gr a b ()
            processNode n = do
                gr <- getGraph
                mm <- getMessages
                nm <- getNodes
                let neigh = nub $ G.neighbors gr n
                let mnode = IM.lookup n nm
                case mnode of
                    Just (Variable mv bds) -> do
                        updateMessages $! map (variableMessage sum n neigh mm) neigh
                    Just (Factor f) -> do
                        updateMessages $! map (factorMessageMaxSum f n neigh mm nm) neigh
                        
                        dbgMsg $ "Factor " ++ show n
                        dbgMsg $ "n = " ++ show n ++ ", neigh = " ++ show neigh ++ ", lookup: " ++
                            show (map (\x -> M.lookup (x,n) mm) neigh) ++
                            ", mmessages: " ++ show (map (factorMessageMaxSum f n neigh mm nm) neigh)
                    _ -> return ()
            
{-                        
Backtracking starts at a node /startNode/ (the root), which must be a variable node.
It then finds x = argmax (sum (incoming (x))) over x. 
It adds BacktrackMessage values for each neighbouring factor to
a list and calls backtrack.
backtrack in turn takes each entry (BTM (s,t) a) in that list, 
selects the maximising configuration c_max by fixing the value of the variabla s to a 
in the FactorMessage (t,s).
For all other connected variables to the factor node t, it then adds
BTM messages to the beginning of the list using variable values from c_max.
Therefore, (BTM (s,t) a) always has /s/ as a variable node, /t/ as a factor node, and /a/ as
the optimal value for /s/.
-}
            backtrack' :: (Show a, Monad (m gr a b), Floating b, Ord b, FGMClass m, IIntegrate a b, G.DynGraph gr) => G.Node -> m gr a b [(G.Node, a)]
            backtrack' startNode = do
              mincoming <- incomingMessages startNode >>= return . sequence
              let incoming = case mincoming of
                    Just i -> i
                    Nothing -> error "backtrack': incoming message was not present."
              nm <- getNodes
              gr <- getGraph              
              let (startValue, endValue) = fromJust $ do
                    node <- IM.lookup startNode nm
                    if isVariable node 
                      then return $ varBounds node 
                      else error "backtrack': startNode must be a variable."
                           
                  -- The incoming messages can only be of this type. Anything else leads to an exception,
                  -- which is ok for now.
                  sumIncoming x = foldl' (\l (MaxSumFactorMessage f _) -> l + f x) 0 incoming
                  argmax' f [] m fm = (m,fm)
                  argmax' f (x:xs) m fm = let (m',fm') | fm < fx = (x,fx)
                                                       | otherwise = (m,fm) 
                                              fx = f x
                                          in argmax' f xs m' fm'
                  
                  (m,mf) = argmax' sumIncoming [(succ startValue)..endValue] startValue (sumIncoming startValue)
                  neigh = sort $ nub $ G.neighbors gr startNode
                  btms = map (\n -> BTM (startNode,n) m) neigh
              dbgMsg $ "backtrack': btms: " ++ show btms
              --return [(startNode,m)]
              backtrack btms [(startNode,m)]
              
            {- Backtracking to find the argmax, i.e. find the optimal variable values.
               Note this is only working for tree-structured graphs.
               For any other graph structure we will have to keep track of which 
               of the variables we have already visited. 
                -}
              -- s: variable node. t: factor node. 
            backtrack [] v = return v
            backtrack (BTM (s,t) a : ms) variableValues = do
              gr <- getGraph
              nm <- getNodes
              mm <- getMessages
              let neigh = sort $ nub $ G.neighbors gr t
                  neigh' = filter (/= s) neigh
                  mfm = M.lookup (t,s) mm
                  MaxSumFactorMessage _ max'f = case mfm of
                    Just m -> m
                    Nothing -> error $ "backtrack: factor message " ++ show (t,s) ++ " could not be found."
                  neighValues = zip neigh (max'f a)
                  neighValues' = filter ((/= s) . fst) neighValues
                  btms = concatMap (makeBTMs gr (s,t)) neighValues'
              dbgMsg $ "backtrack: btms: " ++ show btms
              backtrack (btms ++ ms) (neighValues' ++ variableValues)
            
            makeBTMs gr (s,t) (var,value) = let neigh = filter (/= t) $ sort $ nub $ G.neighbors gr var
                                                makeBTM u = BTM (var, u) value
                                            in map makeBTM neigh
                                             
                  
              
            
{-| Given a factor function f_s with it's node number n_f, all neighbouring nodes, message and node maps, and
    the node n_n to compute the message to, returns the edge (n_f,n_n) with the message \mu_{f_s -> x}(x) or Nothing. 
    Note this differs only very little from /factorMessage/, and these could be made one function with some variability. -}
factorMessageMaxSum :: (Ix a, Integral a, Floating b, Boundsf [a] b) =>
    ([a] -> b)         -- ^ Factor function, f_s
    -> G.Node          -- ^ This factor node
    -> [G.Node]        -- ^ /All/ neighbouring nodes
    -> MessageMap a b  -- ^ The message map
    -> NodeMap a b     -- ^ The node map
    -> G.Node          -- ^ The node to compute the message to
    -> Maybe (G.Edge, Message a b)
factorMessageMaxSum f n neigh mm nm o = mf'
  where neigh'' = sort neigh
        mn = elemIndex o neigh''
        mbds = map getBds neigh''
        -- Incoming messages from neighbouring variable nodes, here including o
        mincoming = map f neigh''
            where f x | x /= o = M.lookup (x,n) mm
                      | otherwise = Just $! Message (const 0)
        getBds node = 
          IM.lookup node nm >>= \v ->
          if isVariable v
          then return $ varBounds v
          else error $ "Error in the graph structure -- node " ++ show v ++ " is a factor node and is connected to a factor node."
                       -- This was a factor node -- should not happen,
                       -- that indicates an error in the graph structure.
        mf' = do
            incoming <- sequence mincoming
            bds <- sequence mbds
            n' <- mn
            let table = factorTableMaxSum (n,o) f bds incoming n' 
                        -- If we move the let into the Message below, the interpreter
                        -- apparently computes the table anew at each call to the Message. Doing it this way ensures that
                        -- the table is computed only once and referenced afterwards.
            --trace ("factorMessageMaxSum: table: " ++ show table) (return ())
            return ((n,o), MaxSumFactorMessage (\a -> fst $ table ! a) (\a -> snd $ table ! a))



factorTableMaxSum :: (Floating b, Num a, Ix a, Boundsf [a] b) => (G.Node, G.Node) -- Just for debugging
    -> ([a] -> b)      -- ^ Function /f/ to compute the integral or sum over (the factor node's function).
    -> [(a,a)]        -- ^ Bounds (inclusive) for /all/ the incoming functions (messages). Sums are computed for these values, must be the same length as the list the function /f/ expects as its first argument.
    -> [Message a b]  -- ^ All the incoming messages into the node we are computing on (which is a factor node).
    -> Int            -- ^ The index /n/ of the argument to /f/ that will be used as index into the returned table.
    -> Array a (b, [a])    -- ^ Contains the value of sum_(x_1,.,x_n,..,x_N) f(x_1,..,x_n,..,x_N) * prod(incoming\\incoming_n) for each value of the /n/'th variable of /f/.
factorTableMaxSum (source,target) f bds incoming n = table -- trace ("from " ++ show source ++ " to " ++ show target) table 
  where
    table = array nbds [(a, int'f a) | a <- range nbds]
    nbds = bds !! n
    sz = rangeSize nbds
    -- int'f x computes \mu_{f_s -> x}(x), Bishop eqn. (8.66).
    -- int'f :: (Boundsf a b) => a -> [a]
    f' = f'factor 0 (+) (log . f) incoming'
    int'f a = let xarg = argmax (as,bs) f'
                  x = f' xarg
                  as = replace n a $ map fst bds 
                  bs = replace n a $ map snd bds
              in (x, xarg) -- for a, return the max. value x and the maximising configuration xarg.

    -- Replace the message coming from the node n for which we are computing the factor message,
    -- with the constant function returning 0.
    incoming' = replace n (Message $! const 0) incoming



-- Computes the term f_s(x,x_1,...,x_M) times the product term of (8.66) in Bishop.
-- f is the factor function, fis are the incoming variable message functions, and xs are the variable values as a list.
-- /op/ is an operator such as (*) or (+). Start would be 1 (for products) or 0 (for sums).
f'factor start op f fis xs = fxs `seq` fxs `op` f'' fis xs -- (f'' fis xs) 
  where fxs = f xs
        f'' as bs = foldl' (\b (func, a) -> b `op` (messageFunction func) a) start (zip as bs)


{-| Replaces the element at a given position n in the list with a'. -}
replace :: Integral i => 
          i     -- ^ The position at which to replace
          -> a   -- ^ The element to put at that position
          -> [a] -- ^ The original list
          -> [a] -- ^ Returns a new list with the element replaced
replace _ _ [] = error "replace: the list is empty or too short."
replace 0 a' (a:as) = a' : as
replace n a' (a:as) = a : replace (n-1) a' as



{-| Compute the message from variable n to factor o, which is the product of all incoming messages
   from all neighbouring nodes of n except for o. 
/op/ is one of /product/ and /sum/, depending on what you want to do with the incoming messages.
-}
variableMessage :: Num b => ([b] -> b) -> G.Node -> [G.Node] -> MessageMap a b -> G.Node -> Maybe (G.Edge, Message a b)
variableMessage op n neigh mm o =
    let neigh' = filter (/= o) neigh
        mincoming = map (\x -> M.lookup (x,n) mm) neigh'
        moutgoing = sequence mincoming >>= \incoming -> 
          let outgoing = Message $! \x -> -- trace ("from var " ++ show n ++ " to factor " ++ show o) 
                                         (op (1 : map (\mf -> (messageFunction mf) x) incoming))
          in return ((n,o), outgoing)
    in moutgoing
{-# INLINE variableMessage #-}
{-# INLINE messageFunction #-}

{- sumProduct :: FGM gr a b ()
sumProduct = do
    (FactorGraph gr) <- getFG -}

{-| Create a test graph, just a chain. -}
testGraph :: Int -> Int -> FactorGraph Gr Int Float
testGraph n k = fg
    where
        fg = FactorGraph { fgGraph = undir $ G.mkUGraph (vnodes ++ fnodes) ledges,
                           fgMessages = mm,
                           fgNodes = nm }
        nm = IM.fromList (zip (vnodes ++ fnodes) (variables ++ factors))
        mm = M.empty
        variables = map (\x -> Variable Nothing (0,k-1)) vnodes
        factors = map (\(x,y) -> Factor fac) edgepairs
        fac [x,y] = let e = fromIntegral ( -( abs $! y - x - 1) )
                    in exp e
        vnodes = [1..n]
        fnodes = [(n+1)..(2*n-1)]
        ledges = edgepairs
        edgepairs1 = 1 : (concat [[x,x] | x <- [2..(n-1)]]) ++ [n]
        edgepairs2 = concat [[x,x] | x <- fnodes]
        edgepairs = zip edgepairs1 edgepairs2

{-| Create a test graph, just a chain. -}
testGraph2 :: FactorGraph Gr Int Float
testGraph2 = fg
    where
        fg = FactorGraph { fgGraph = undir $ G.mkUGraph (vnodes ++ fnodes) ledges,
                           fgMessages = mm,
                           fgNodes = nm }
        nm = IM.fromList (zip (vnodes ++ fnodes) (variables ++ factors))
        mm = M.empty
        variables = map (\x -> Variable Nothing (0,9)) vnodes
        factors = map (\(x,y) -> Factor fac) edgepairs
        fac [x,y] = let e = fromIntegral ( -( abs $! y - x - 1) )
                    in exp e
        vnodes = [1..8]
        fnodes = [n..m] where { n = (last vnodes) + 1; m = n + length vnodes - 1 }
        ledges = edgepairs
        edgepairs1 = 1 : (concat [[x,x] | x <- [2..last vnodes - 1]]) ++ [last vnodes]
        edgepairs2 = concat [[x,x] | x <- fnodes]
        edgepairs = zip edgepairs1 edgepairs2