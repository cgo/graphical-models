{-# LANGUAGE NoMonomorphismRestriction #-}
-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Main (
    main
) where

import GM
import Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.Graphviz
import Data.Graph.Inductive.PatriciaTree
import Data.List

main = do
    let fg = testGraph 640 12
        mm = fgMessages fg
        nm = fgNodes fg
    let g = fgGraph fg
    let s = graphviz' g
    writeFile "graph.dot" s
    let sp = (sumProduct :: FGM Gr Int Float ())
        maxsum = (maxSum :: FGM Gr Int Float [(G.Node,Int)])
        -- w = runFGMDebugLog fg nm mm sp
        --(ms,w) = runFGM fg sp'
        ms = runFGM fg sp'
        --(optVars,w') = runFGMDebugLog fg maxsum
        optVars = runFGM fg maxsum
        sp' = sp >> normalisationConstant 1 >>= \z' -> 
          sequence (map (\x -> marginal x >>= \f -> 
                          return (\a -> f a * z')) [1..8])
    -- putStrLn $ intercalate "\n" w'
    --mapM_ (\x -> putStrLn "\n" >> mapM_ (\m -> (putStrLn . show . m) x) ms) [1..8]
    --putStrLn $ show $ head ms $ 1
    putStrLn $ "Optimal variable values: " ++ show optVars
    return ()
