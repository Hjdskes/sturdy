# Sturdy ![build-status](https://travis-ci.org/svenkeidel/sturdy.svg?branch=master)

Sturdy is a library to create sound abstract interpreters in Haskell.
To build, install the [Stack](https://www.haskellstack.org/) build tool and run `stack build` from the root directory of the project.

The sturdy project currently contains concrete and abstract interpreters for three languages:
* _PCF_, a higher-order functional language with numbers
* _While_, an imperative language with conditionals and while loops
* _Stratego_, a language for program transformations