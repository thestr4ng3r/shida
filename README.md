# 羊歯 Shida

Shida is an experimental SMT solver for Bit Vectors written in Haskell that has
been developed alongside a paper on the same topic (available in [doc](doc))
for the seminar [Automated Reasoning](https://www21.in.tum.de/teaching/sar/SS20/) at TUM.

**Disclaimer**: If you are looking for an efficient, production quality solver,
do not use this. Use something like [Z3](https://github.com/Z3Prover/z3) instead.

## Usage

Build:
```
stack build
```

Run all tests:
```
stack test
```

The solver can be used conveniently in ghci, for example:
```Haskell
$ stack repl
λ> f = Atom $ (uVar 8 "a" :-: uConst (13::Word8)) :==: uConst (29::Word8)
λ> f
((a - 0b00001101) = 0b00011101)
λ> solve f
Solution (fromList [("a",0b00101010)])
```

More examples for formulas can be found in [test/SolveTest.hs](test/SolveTest.hs).

The most important solving functions are:

```Haskell
-- |Solve to a single solution
solve :: Formula -> SolveResult Solution

-- |Solve to all solutions as a lazy list
solveAll :: Formula -> SolveResult [Solution]

-- |Solve incrementally to a single solution
-- This can be significantly faster or slower than solve depending on the
-- formula, see the paper for more info.
solveIncremental :: Int -> Formula -> SolveResult Solution
```

## About

Created by Florian Märkl.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
