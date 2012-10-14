module GhcPlugins.Comparisons ( plugin ) where

import Data.List ( intersperse )

import GhcPlugins

import GhcPlugins.Comparisons.Pass

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos = do
  reinitializeGlobals
  return $ intersperse pass todos
  where
    debug = "debug" `elem` opts
    pass = CoreDoPluginPass "Comparisons" (transformProgram debug)
