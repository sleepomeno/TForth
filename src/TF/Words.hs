{-# LANGUAGE OverloadedStrings  #-}

module TF.Words where

import Prelude hiding (until, drop, Word)
import qualified Data.Map as M
import Control.Lens
-- import           Lens.Family2
import Control.Monad
import Control.Monad.Free
import           TF.Types hiding (depth)
import TF.WordsBuilder

-----------
-- WORDS --
-----------
-- number = view word <$> (buildWord $ do
number = buildWord $ do
   numberParsed
   named "a number"
   effect "( -- n )"

create = buildWord $ do
  parsing "create"
  named "create"
  effect "( D'name' -- )"

colon = buildWord $ do
  parsing ":"
  named "colon"
  entering COMPILESTATE

semicolon = buildWord $ do
  parsing ";"
  named "semicolon"
  undefinedInterpretation
  compilationStart
  entering INTERPRETSTATE
  compilationEnd

-- wordToHasEffect :: Word Semantics -> HasEffect
-- wordToHasEffect w = HasEffect (w ^. name) effect
--   where
--     [effects] = w ^.. execution._Wrapped._Sem.effectsOfStack
--     [effect] = TF.Util.allEffects effects

-- saveCallingDefinition = wordToHasEffect $ (^. word) $ buildWord $ do
--   parsing "saveCallingDefinition"
--   named "saveCallingDefinition"
--   effect "( R: -- nest-sys )"

-- pushAddr = wordToHasEffect $ (^. word) $ buildWord $ do
--   parsing "pushAddr"
--   named "pushAddr"
--   effect "( -- a-addr )"
--   effect "( R: -- nest-sys2 )"

does = buildWord $ do
  parsing "does>"
  named "does"
  undefinedInterpretation

                
store = buildWord $ do
  parsing "!"
  named "store"
  describing "Store x at a-addr."
  effect "( x *x -- )"

numberSign = buildWord $ do
  parsing "#"
  named "number-sign"
  effect "( u1 -- u2 / d1 -- d2 )"

numberSignGreater = buildWord $ do
  parsing "#>"
  named "number-sign-greater"
  describing "Drop xd.  Make the pictured numeric output string available as a character string.  c-addr and u specify the resulting character string.  A program may replace characters within the string." 
  effect "( xd -- c-addr u )"
  -- effect "( xt -- c-addr u )"

if' = buildWord $ do
  parsing "if"
  named "if"
  undefinedInterpretation
  runtimeStart
  effect "( x -- )"
  runtimeEnd


then' = buildWord $ do
  parsing "then"
  named "then"
  undefinedInterpretation
  runtimeStart
  effect "( -- )"
  describing "Continue execution."
  runtimeEnd

else' = buildWord $ do
  parsing "else"
  named "else"
  undefinedInterpretation
  runtimeStart
  effect "( -- )"
  describing "Continue execution at the location given by the resolution of orig2."
  runtimeEnd
  
  

numberSignS = buildWord $ do
  parsing "#S"
  named "number-sign-s"
  describing "Convert one digit of u1|d1 according to the rule for #.  Continue conversion until the quotient is zero.  u2|d2 is zero.  An ambiguous condition exists if #S executes outside of a <# #> delimited number conversion."
  effect "( u1 -- u2 / d1 -- d2 ) "

tick = buildWord $ do
  parsing "'"
  named "tick"
  describing "Skip leading space delimiters.  Parse name delimited by a space.  Find name and return xt, the execution token for name.  An ambiguous condition exists if name is not found.\n\nWhen interpreting, ' xyz EXECUTE is equivalent to xyz."
  effect "( 'name':[ EFF1 ] -- xt:[ EFF1 ] )"

bracketTick = buildWord $ do
  parsing "[']"
  named "bracket-tick"
  describing "Skip leading space delimiters.  Parse name delimited by a space.  Find name and return xt, the execution token for name.  An ambiguous condition exists if name is not found.\n\nWhen interpreting, ' xyz EXECUTE is equivalent to xyz."
  effect "( 'name':[ EFF1 ] -- xt:[ EFF1 ] )"
  immediate

paren = buildWord $ do
  parsing "("
  named "paren"
  immediate
  describing "Parse ccc delimited by ) (right parenthesis).  ( is an immediate word.\n\nThe number of characters in ccc may be zero to the number of characters in the parse area."
  effect "( 'ccc<paren>' -- )"

star = buildWord $ do
  parsing "*"
  named "star"
  describing "Multiply n1|u1 by n2|u2 giving the product n3|u3."
  effect "( n1 n2 -- n3 / u1 u2 -- u3 )"

starSlash = buildWord $ do
  parsing "*/"
  named "star-slash"
  describing "Multiply n1 by n2 producing the intermediate double-cell result d.  Divide d by n3 giving the single-cell quotient n4.  An ambiguous condition exists if n3 is zero or if the quotient n4 lies outside the range of a signed number.  If d and n3 differ in sign, the implementation-defined result returned will be the same as that returned by either the phrase >R M* R> FM/MOD SWAP DROP or the phrase >R M* R> SM/REM SWAP DROP."
  effect "( n1 n2 n3 -- n4 )"

starSlashMod = buildWord $ do
  parsing "*/mod"
  named "star-slash-mod"
  describing "Multiply n1 by n2 producing the intermediate double-cell result d.  Divide d by n3 producing the single-cell remainder n4 and the single-cell quotient n5.  An ambiguous condition exists if n3 is zero, or if the quotient n5 lies outside the range of a single-cell signed integer.  If d and n3 differ in sign, the implementation-defined result returned will be the same as that returned by either the phrase >R M* R> FM/MOD or the phrase >R M* R> SM/REM."
  effect "( n1 n2 n3 -- n4 n5 )"

plus = buildWord $ do
  parsing "+"
  named "plus"
  describing "Add n2|u2 to n1|u1, giving the sum n3|u3."
  effect "( n1 n2 -- n3 & u1 u2 -- u3 )"

plusStore = buildWord $ do
  parsing "+!"
  named "plus-store"
  describing "Add n|u to the single-cell number at a-addr."
  effect "( n *n -- / u *u -- )"

plusLoop = buildWord $ do
  parsing "+loop"
  named "plus-loop"
  interpretationStart >> undefinedEffect >> interpretationEnd
  runtimeStart
  -- effect "( n -- ) ( R: loop-sys1 -- | loop-sys2 )"
  effect "( n -- )"
  describing "An ambiguous condition exists if the loop control parameters are unavailable.  Add n to the loop index.  If the loop index did not cross the boundary between the loop limit minus one and the loop limit, continue execution at the beginning of the loop.  Otherwise, discard the current loop control parameters and continue execution immediately following the loop."
  runtimeEnd

comma = buildWord $ do
  parsing ","
  named "comma"
  effect "( x -- )"
  describing "Reserve one cell of data space and store x in the cell.  If the data-space pointer is aligned when , begins execution, it will remain aligned when , finishes execution.  An ambiguous condition exists if the data-space pointer is not aligned prior to execution of ,."

minus = buildWord $ do
  parsing "-"
  named "minus"
  effect "( n1 n2 -- n3 & u1 u2 -- u3 )"
  describing "Subtract n2|u2 from n1|u1, giving the difference n3|u3."

dot = buildWord $ do
  parsing "."
  named "dot"
  effect "( n -- )"
  describing "Display n in free field format."

dotquote = buildWord $ do
  parsing ".\""
  named "dot-quote"
  compilationStart
  effect "( 'ccc<\">' -- )"
  describing "Parse ccc delimited by \" (double-quote).  Append the run-time semantics given below to the current definition."
  compilationEnd
  runtimeStart
  effect "( -- )"
  describing "Display ccc."
  runtimeEnd

slash = buildWord $ do
  parsing "/"
  named "slash"
  effect "( n1 n2 -- n3 )"
  describing "Divide n1 by n2, giving the single-cell quotient n3.  An ambiguous condition exists if n2 is zero.  If n1 and n2 differ in sign, the implementation-defined result returned will be the same as that returned by either the phrase >R S>D R> FM/MOD SWAP DROP or the phrase >R S>D R> SM/REM SWAP DROP."

slashMod = buildWord $ do
  parsing "/mod"
  named "slash-mod"
  effect "( n1 n2 -- n3 n4 )"
  describing "Divide n1 by n2, giving the single-cell remainder n3 and the single-cell quotient n4.  An ambiguous condition exists if n2 is zero. If n1 and n2 differ in sign, the implementation-defined result returned will be the same as that returned by either the phrase >R S>D R> FM/MOD or the phrase >R S>D R> SM/REM."

zeroLess = buildWord $ do
  parsing "0<"
  named "zero-less"
  effect "( n -- flag )"
  describing "flag is true if and only if n is less than zero."

zeroEquals = buildWord $ do
  parsing "0="
  named "zero-equals"
  effect "( x -- flag )"
  describing "flag is true if and only if x is equal to zero."

onePlus = buildWord $ do
  parsing "1+"
  named "one-plus"
  effect "( n1|u1 -- n2|u2 )"
  describing "Add one (1) to n1|u1 giving the sum n2|u2."

oneMinus = buildWord $ do
  parsing "1-"
  named "one-minus"
  effect "( n1|u1 -- n2|u2 )"
  describing "Subtract one (1) from n1|u1 giving the difference n2|u2."

twoStore = buildWord $ do
  parsing "2!"
  named "two-store"
  effect "( x1 x2 a-addr -- )"
  describing "Store the cell pair x1 x2 at a-addr, with x2 at a-addr and x1 at the next consecutive cell.  It is equivalent to the sequence SWAP OVER ! CELL+ !."

twoStar = buildWord $ do
  parsing "2*"
  named "two-star"
  effect "( x1 -- x2 )"
  describing "x2 is the result of shifting x1 one bit toward the most-significant bit, filling the vacated least-significant bit with zero."

twoSlash = buildWord $ do
  parsing "2/"
  named "two-slash"
  effect "( x1 -- x2 )"
  describing "x2 is the result of shifting x1 one bit toward the least-significant bit, leaving the most-significant bit unchanged."

twoFetch = buildWord $ do
  parsing "2@"
  named "two-fetch"
  effect "( a-addr -- x1 x2 )"
  describing "Fetch the cell pair x1 x2 stored at a-addr.  x2 is stored at a-addr and x1 at the next consecutive cell.  It is equivalent to the sequence DUP CELL+ @ SWAP @."

twoDrop = buildWord $ do
  parsing "2drop"
  named "two-drop"
  effect "( x1 x2 -- )"
  describing "Drop cell pair x1 x2 from the stack."

twoDup = buildWord $ do
  parsing "2dup"
  named "two-dupe"
  effect "( x1 x2 -- x1 x2 x1 x2 )"
  describing "Duplicate cell pair x1 x2."

twoOver = buildWord $ do
  parsing "2over"
  named "two-over"
  effect "( x1 x2 x3 x4 -- x1 x2 x3 x4 x1 x2 )"
  describing "Copy cell pair x1 x2 to the top of the stack."

twoSwap = buildWord $ do
  parsing "2swap"
  named "two-swap"
  effect "( x1 x2 x3 x4 -- x3 x4 x1 x2 )"
  describing "Exchange the top two cell pairs."

lessThan = buildWord $ do
  parsing "<"
  named "less-than"
  effect "( n1 n2 -- flag )"
  describing "flag is true if and only if n1 is less than n2."

lessNumberSign = buildWord $ do
  parsing "<#"
  named "less-number-sign"
  effect "( -- )"
  describing "Initialize the pictured numeric output conversion process."

equals = buildWord $ do
  parsing "="
  named "equals"
  effect "( x1 x2 -- flag )"
  describing "flag is true if and only if x1 is bit-for-bit the same as x2."

greaterThan = buildWord $ do
  parsing ">"
  named "greater-than"
  effect "( n1 n2 -- flag )"
  describing "flag is true if and only if n1 is greater than n2."

toBody = buildWord $ do
  parsing ">body"
  named "to-body"
  effect "( xt -- a-addr )"
  describing "a-addr is the data-field address corresponding to xt.  An ambiguous condition exists if xt is not for a word defined via CREATE."

toIn = buildWord $ do
  parsing ">in"
  named "to-in"
  effect "( -- a-addr )"
  describing "a-addr is the address of a cell containing the offset in characters from the start of the input buffer to the start of the parse area."

toNumber = buildWord $ do
  parsing ">number"
  named "to-number"
  effect "( ud1 c-addr1 u1 -- ud2 c-addr2 u2 )"
  describing "ud2 is the unsigned result of converting the characters within the string specified by c-addr1 u1 into digits, using the number in BASE, and adding each into ud1 after multiplying ud1 by the number in BASE.  Conversion continues left-to-right until a character that is not convertible, including any “+” or “-”, is encountered or the string is entirely converted.  c-addr2 is the location of the first unconverted character or the first character past the end of the string if the string was entirely converted.  u2 is the number of unconverted characters in the string.  An ambiguous condition exists if ud2 overflows during the conversion."

toR = buildWord $ do
  parsing ">r"
  named "to-r"
  undefinedInterpretation
  compilationStart
  effect "( x -- )  ( R:  -- x )"
  describing "Move x to the return stack."
  compilationEnd

questionDup = buildWord $ do
  parsing "?dup"
  named "question-dupe"
  effect "( x -- x | x x )"
  describing "Duplicate x if it is non-zero."

fetch = buildWord $ do
  parsing "@"
  named "fetch"
  -- effect "( a-addr -- x )"
  effect "( *x -- x )"
  describing "x is the value stored at a-addr."

abort = buildWord $ do
  parsing "abort"
  named "abort"
  describing "Empty the data stack and perform the function of QUIT, which includes emptying the return stack, without displaying a message."

abortQuote = buildWord $ do
  parsing "abort\""
  named "abort-quote"
  undefinedInterpretation
  compilationStart
  effect "( 'ccc<quote>' -- )"
  describing "Parse ccc delimited by a \" (double-quote).  Append the run-time semantics given below to the current definition. "
  compilationEnd
  runtimeStart
  -- effect "( i*x x1 --  | i*x ) ( R: j*x --  | j*x )"
  describing "Remove x1 from the stack.  If any bit of x1 is not zero, display ccc and perform an implementation-defined abort sequence that includes the function of ABORT."
  runtimeEnd

abs' = buildWord $ do
  parsing "abs"
  named "abs"
  effect "( n -- u )"
  describing "u is the absolute value of n."
  
accept = buildWord $ do
  parsing "accept"
  -- effect "( c-addr +n1 -- +n2 )"
  effect "( c-addr n1 -- n2 )"
  describing "Receive a string of at most +n1 characters.  An ambiguous condition exists if +n1 is zero or greater than 32,767.  Display graphic characters as they are received.  A program that depends on the presence or absence of non-graphic characters in the string has an environmental dependency.  The editing functions, if any, that the system performs in order to construct the string are implementation-defined.\n\n Input terminates when an implementation-defined line terminator is received.  When input terminates, nothing is appended to the string, and the display is maintained in an implementation-defined way.\n\n +n2 is the length of the string stored at c-addr."

align = buildWord $ do
  parsing "align"
  named "align"
  effect "( -- )"
  describing "If the data-space pointer is not aligned, reserve enough space to align it."

aligned = buildWord $ do
  parsing "aligned"
  effect "( addr -- a-addr )"
  describing "a-addr is the first aligned address greater than or equal to addr."

allot = buildWord $ do
  parsing "allot"
  effect "( n -- )"
  describing "If n is greater than zero, reserve n address units of data space.  If n is less than zero, release |n| address units of data space.  If n is zero, leave the data-space pointer unchanged.\n\n If the data-space pointer is aligned and n is a multiple of the size of a cell when ALLOT begins execution, it will remain aligned when ALLOT finishes execution.\n\n If the data-space pointer is character aligned and n is a multiple of the size of a character when ALLOT begins execution, it will remain character aligned when ALLOT finishes execution."

and' = buildWord $ do
  parsing "and"
  effect "( x1 x2 -- x3 )"
  describing "x3 is the bit-by-bit logical “and” of x1 with x2."

base = buildWord $ do
  parsing "base"
  named "base"
  effect "( -- a-addr )"
  describing "a-addr is the address of a cell containing the current number-conversion radix {{2...36}}."

bl = buildWord $ do
  parsing "bl"
  named "bl"
  effect "( -- char )"
  describing "char is the character value for a space."

cStore = buildWord $ do
  parsing "c!"
  named "c-store"
  effect "( char c-addr -- )"
  describing "Store char at c-addr.  When character size is smaller than cell size, only the number of low-order bits corresponding to character size are transferred."

cComma = buildWord $ do
  parsing "c,"
  named "c-comma"
  effect "( char -- )"
  describing "Reserve space for one character in the data space and store char in the space.  If the data-space pointer is character aligned when C, begins execution, it will remain character aligned when C, finishes execution.  An ambiguous condition exists if the data-space pointer is not character-aligned prior to execution of C,."

cFetch = buildWord $ do
  parsing "c@"
  named "c-fetch"
  effect "( *char -- char )"
  describing "Fetch the character stored at c-addr.  When the cell size is greater than character size, the unused high-order bits are all zeroes."

cellPlus = buildWord $ do
  parsing "cell+"
  named "cell-plus"
  effect "( a-addr1 -- a-addr2 )"
  describing "Add the size in address units of a cell to a-addr1, giving a-addr2."

cells = buildWord $ do
  parsing "cells"
  effect "( n1 -- n2 )"
  describing "n2 is the size in address units of n1 cells."

char = buildWord $ do
  parsing "char"
  named "char"
  effect "( 'name' -- char )"
  describing "Skip leading space delimiters.  Parse name delimited by a space.  Put the value of its first character onto the stack."

charPlus = buildWord $ do
  parsing "char+"
  named "char-plus"
  effect "( c-addr1 -- c-addr2 )"
  describing "Add the size in address units of a character to c-addr1, giving c-addr2."

chars = buildWord $ do
  parsing "chars"
  effect "( n1 -- n2 )"
  describing "n2 is the size in address units of n1 characters."

constant = buildWord $ do
  parsing "constant"
  named "constant"
  effect "( 'name' -- )"
  describing "Skip leading space delimiters.  Parse name delimited by a space.  Create a definition for name with the execution semantics defined below.\n\n name is referred to as a 'constant'."
  -- skip execution stuff

count = buildWord $ do
  parsing "count"
  effect "( c-addr1 -- c-addr2 u )"
  describing "Return the character string specification for the counted string stored at c-addr1.  c-addr2 is the address of the first character after c-addr1.  u is the contents of the character at c-addr1, which is the length in characters of the string at c-addr2."

cr = buildWord $ do
  parsing "cr"
  named "cr"
  effect "( -- )"
  describing "Cause subsequent output to appear at the beginning of the next line."

decimal = buildWord $ do
  parsing "decimal"
  named "decimal"
  effect "( -- )"
  describing "Set the numeric conversion radix to ten (decimal)."

depth = buildWord $ do
  parsing "depth"
  effect "( -- +n )"
  describing "+n is the number of single-cell values contained in the data stack before +n was placed on the stack."

drop = buildWord $ do
  parsing "drop"
  named "drop"
  effect "( x -- )"
  describing "Remove x from the stack."

dup = buildWord $ do
  parsing "dup"
  named "dup"
  effect "( x1 -- x1 x1 )"
  describing "Duplicate x"

emit = buildWord $ do
  parsing "emit"
  effect "( x -- )"
  describing "If x is a graphic character in the implementation-defined character set, display x.  The effect of EMIT for all other values of x is implementation-defined.\n\n When passed a character whose character-defining bits have a value between hex 20 and 7E inclusive, the corresponding standard character, specified by 3.1.2.1 Graphic characters, is displayed.  Because different output devices can respond differently to control characters, programs that use control characters to perform specific functions have an environmental dependency.  Each EMIT deals with only one character."

-- environmentQuery = buildWord $ do
--   parsing "environment?"
--   named "environment-query"
--   effect "( c-addr u -- false | i*x true )"
--   describing "c-addr is the address of a character string and u is the string’s character count.  u may have a value in the range from zero to an implementation-defined maximum which shall not be less than 31.  The character string should contain a keyword from 3.2.6 Environmental queries or the optional word sets to be checked for correspondence with an attribute of the present environment.  If the system treats the attribute as unknown, the returned flag is false;  otherwise, the flag is true and the i*x returned is of the type specified in the table for the attribute queried."

-- evaluate = buildWord $ do
--   parsing "evaluate"
--   effect "( i*x c-addr u -- j*x )"
--   describing "Save the current input source specification.  Store minus-one (-1) in SOURCE-ID if it is present.  Make the string described by c-addr and u both the input source and input buffer, set >IN to zero, and interpret.  When the parse area is empty, restore the prior input source specification.  Other stack effects are due to the words EVALUATEd."

execute = buildWord $ do
  parsing "execute"
  effect "( -- )"
  -- effect "( i*x xt -- j*x )"
  describing "Remove xt from the stack and perform the semantics identified by it.  Other stack effects are due to the word EXECUTEd."

exit = buildWord $ do
  undefinedInterpretation
  parsing "exit"
  -- effect "( -- ) ( R: nest-sys -- )"
  effect "( -- )"
  describing "Return control to the calling definition specified by nest-sys.  Before executing EXIT within a do-loop, a program shall discard the loop-control parameters by executing UNLOOP."

fill = buildWord $ do
  parsing "fill"
  effect "( c-addr u char -- )"
  describing "If u is greater than zero, store char in each of u consecutive characters of memory beginning at c-addr."

find = buildWord $ do
  parsing "find"
  effect "( c-addr -- c-addr n / c-addr -- xt n )"
  describing "Find the definition named in the counted string at c-addr.  If the definition is not found, return c‑addr and zero.  If the definition is found, return its execution token xt.  If the definition is immediate, also return one (1), otherwise also return minus-one (-1).  For a given string, the values returned by FIND while compiling may differ from those returned while not compiling."

fmMod = buildWord $ do
  parsing "fm/mod"
  named "f-m-slash-mod"
  effect "( d1 n1 -- n2 n3 )"
  describing "Divide d1 by n1, giving the floored quotient n3 and the remainder n2.  Input and output stack arguments are signed.  An ambiguous condition exists if n1 is zero or if the quotient lies outside the range of a single-cell signed integer."

here = buildWord $ do
  parsing "here"
  effect "( -- addr )"
  describing "addr is the data-space pointer."

hold = buildWord $ do
  parsing "hold"
  effect "( char -- )"
  describing "Add char to the beginning of the pictured numeric output string.  An ambiguous condition exists if HOLD executes outside of a <# #> delimited number conversion."

---
i = buildWord $ do
  parsing "i"
  undefinedInterpretation
  effect "( -- n|u )"
  describing "n|u is a copy of the current (innermost) loop index.  An ambiguous condition exists if the loop control parameters are unavailable."

invert = buildWord $ do
  parsing "invert"
  effect "( x1 -- x2 )"
  describing "Invert all bits of x1, giving its logical inverse x2."

j = buildWord $ do
  parsing "j"
  effect "( -- n|u )"
  describing "n|u is a copy of the next-outer loop index.  An ambiguous condition exists if the loop control parameters of the next-outer loop, loop-sys1, are unavailable."

key = buildWord $ do
  parsing "key"
  effect "( -- char )"
  describing "Receive one character char, a member of the implementation-defined character set.  Keyboard events that do not correspond to such characters are discarded until a valid character is received, and those events are subsequently unavailable.\n\n All standard characters can be received.  Characters received by KEY are not displayed.\n\n Any standard character returned by KEY has the numeric value specified in 3.1.2.1 Graphic characters.  Programs that require the ability to receive control characters have an environmental dependency."

leave = buildWord $ do
  parsing "leave"
  undefinedInterpretation
  effect "( -- )"

lshift = buildWord $ do
  parsing "lshift"
  named "l-shift"
  effect "( x1 u -- x2 )"
  describing "Perform a logical left shift of u bit-places on x1, giving x2.  Put zeroes into the least significant bits vacated by the shift.  An ambiguous condition exists if u is greater than or equal to the number of bits in a cell."

mStar = buildWord $ do
  parsing "m*"
  named "m-star"
  effect "( n1 n2 -- d )"
  describing "d is the signed product of n1 times n2."


  --
max = buildWord $ do
  parsing "max"
  effect "( n1 n2 -- n3 )"
  describing "n3 is the greater of n1 and n2."

min = buildWord $ do
  parsing "min"
  effect "( n1 n2 -- n3 )"
  describing "n3 is the lesser of n1 and n2."

mod = buildWord $ do
  parsing "mod"
  effect "( n1 n2 -- n3 )"
  describing "Divide n1 by n2, giving the single-cell remainder n3.  An ambiguous condition exists if n2 is zero.  If n1 and n2 differ in sign, the implementation-defined result returned will be the same as that returned by either the phrase >R S>D R> FM/MOD DROP or the phrase >R S>D R> SM/REM DROP."

move = buildWord $ do
  parsing "move"
  effect "( addr1 addr2 u -- )"
  describing "If u is greater than zero, copy the contents of u consecutive address units at addr1 to the u consecutive address units at addr2.  After MOVE completes, the u consecutive address units at addr2 contain exactly what the u consecutive address units at addr1 contained before the move."

negate = buildWord $ do
  parsing "negate"
  effect "( n1 -- n2 )"
  describing "Negate n1, giving its arithmetic inverse n2."

or = buildWord $ do
  parsing "or"
  -- effect "( x1 x2 -- x3 )"
  effect "( x x -- x )"
  describing "x3 is the bit-by-bit inclusive-or of x1 with x2."

over = buildWord $ do
  parsing "over"
  effect "( x1 x2 -- x1 x2 x1 )"
  describing "Place a copy of x1 on top of the stack."

quit = buildWord $ do
  parsing "quit"
  -- effect "( -- )  ( R:  i*x -- )"
  effect "( -- )"

rFrom = buildWord $ do
  parsing "r>"
  named "r-from"
  undefinedInterpretation
  -- effect "( -- x )  ( R:  x -- )"
  effect "( -- x )"
  describing "Move x from the return stack to the data stack."

rFetch = buildWord $ do
  parsing "r@"
  named "r-fetch"
  undefinedInterpretation
  -- effect "( -- x )  ( R:  x -- x )"
  effect "( -- x )"
  describing "Copy x from the return stack to the data stack."

recurse = buildWord $ do
  parsing "recurse"
  undefinedInterpretation
  effect "( -- )"
  describing "Append the execution semantics of the current definition to the current definition.  An ambiguous condition exists if RECURSE appears in a definition after DOES>."

rot = buildWord $ do
  parsing "rot"
  effect "( x1 x2 x3 -- x2 x3 x1 )"
  describing "Rotate the top three stack entries."

rShift = buildWord $ do
  parsing "rShift"
  effect "( x1 u -- x2 )"
  describing "Perform a logical right shift of u bit-places on x1, giving x2.  Put zeroes into the most significant bits vacated by the shift.  An ambiguous condition exists if u is greater than or equal to the number of bits in a cell."

sQuote = buildWord $ do
  parsing "s\""
  undefinedInterpretation
  compilationStart
  effect "( 'ccc<\">' -- )"
  describing "Parse ccc delimited by \" (double-quote).  Append the run-time semantics given below to the current definition."
  compilationEnd
  runtimeStart
  effect "( -- c-addr u )"
  describing "Return c-addr and u describing a string consisting of the characters ccc.  A program shall not alter the returned string."
  runtimeEnd

sToD = do
  parsing "s>d"
  named "s-to-d"
  effect "( n -- d )"

sign = do
  parsing "sign"
  effect "( n -- )"

smslashrem = do
  parsing "sm/rem"
  effect "( d n -- n n )"

source = do
  parsing "source"
  effect "( -- c-addr u )"

space = do
  parsing "space"
  effect "( -- )"

spaces = do
  parsing "spaces"
  effect "( n -- )"

state = do
  parsing "state"
  effect "( -- a-addr )"

type' = do
  parsing "type"
  effect "( c-addr u -- )"

uDot = do
  parsing "u."
  effect "( u -- )"

uLessThan = do
  parsing "u<"
  named "u-less-than"
  effect "( u u -- flag )"

umStar = do
  parsing "um*"
  named "u-m-star"
  effect "( u u -- ud )"

umMod = do
  parsing "um/mod"
  named "u-m-slash-mod"
  effect "( ud u -- u u )"

xor = do
  parsing "xor"
  effect "( x x -- x )"
  

  



do' = buildWord $ do
  parsing "do"
  undefinedInterpretation
  compilationStart
  -- effect "( C: -- do-sys )"
  describing "Place do-sys onto the control-flow stack.  Append the run-time semantics given below to the current definition.  The semantics are incomplete until resolved by a consumer of do-sys such as LOOP."
  compilationEnd
  runtimeStart
  -- effect "( n1|u1 n2|u2 -- ) ( R: -- loop-sys )"
  effect "( n1|u1 n2|u2 -- )"
  describing "Set up loop control parameters with index n2|u2 and limit n1|u1. An ambiguous condition exists if n1|u1 and n2|u2 are not both the same type.  Anything already on the return stack becomes unavailable until the loop-control parameters are discarded."
  runtimeEnd

loop = buildWord $ do
  parsing "loop"
  undefinedInterpretation
  compilationStart
  -- effect "( C: do-sys -- )"
  describing "Append the run-time semantics given below to the current definition.  Resolve the destination of all unresolved occurrences of LEAVE between the location given by do-sys and the next location for a transfer of control, to execute the words following the LOOP."
  compilationEnd
  runtimeStart
  -- effect "( -- ) ( R:  loop-sys1 --  | loop-sys2 )"
  effect "( -- )"
  describing "An ambiguous condition exists if the loop control parameters are unavailable.  Add one to the loop index.  If the loop index is then equal to the loop limit, discard the loop parameters and continue execution immediately following the loop.  Otherwise continue execution at the beginning of the loop."
  runtimeEnd

postpone = buildWord $ do
  parsing "postpone"
  undefinedInterpretation
  compilationStart
  describing "Skip leading space delimiters.  Parse name delimited by a space.  Find name.  Append the compilation semantics of name to the current definition.  An ambiguous condition exists if name is not found."
  effect "( 'name' -- )"
  compilationEnd

immediate' = buildWord $ do
  parsing "immediate"
  describing "Make the most recent definition an immediate word.  An ambiguous condition exists if the most recent definition does not have a name."
  effect "( -- )"

begin = buildWord $ do
  parsing "begin"
  undefinedInterpretation
  compilationStart
  -- effect "( C: -- dest )"
  describing "Put the next location for a transfer of control, dest, onto the control flow stack.  Append the run-time semantics given below to the current definition."
  compilationEnd
  runtimeStart
  effect "( -- )"
  describing "Continue execution."
  runtimeEnd

until = buildWord $ do
  parsing "until"
  undefinedInterpretation
  compilationStart
  -- effect "( C: dest -- )"
  describing "Append the run-time semantics given below to the current definition, resolving the backward reference dest."
  compilationEnd
  runtimeStart
  effect "( x -- )"
  describing "If all bits of x are zero, continue execution at the location specified by dest."
  runtimeEnd

while = buildWord $ do
  parsing "while"
  named "while"
  undefinedInterpretation
  compilationStart
  -- effect "( C: dest -- orig dest )"
  describing "Put the location of a new unresolved forward reference orig onto the control flow stack, under the existing dest.  Append the run-time semantics given below to the current definition.  The semantics are incomplete until orig and dest are resolved (e.g., by REPEAT)."
  compilationEnd
  runtimeStart
  effect "( x -- )"
  describing "If all bits of x are zero, continue execution at the location specified by the resolution of orig."

repeat = buildWord $ do
  parsing "repeat"
  undefinedInterpretation
  compilationStart
  -- effect "( C: orig dest -- )"
  describing "Append the run-time semantics given below to the current definition, resolving the backward reference dest.  Resolve the forward reference orig using the location following the appended run-time semantics."
  compilationEnd
  runtimeStart
  effect "( -- )"
  describing "Continue execution at the location given by dest."
  runtimeEnd

swap = buildWord $ do
  parsing "swap"
  effect "( x1 x2 -- x2 x1 )"

leftBracket = buildWord $ do
  parsing "["
  named "left-bracket"
  undefinedInterpretation
  compilationStart
  entering INTERPRETSTATE
  effect "( -- )"
  compilationEnd

literal = buildWord $ do
  parsing "literal"
  undefinedInterpretation
  compilationStart
  effect "( x -- )"
  describing "Append the run-time semantics given below to the current definition."
  compilationEnd
  runtimeStart
  effect "( -- x )"
  describing "Place x on the stack."
  runtimeEnd

pad = buildWord $ do
  parsing "pad"
  effect "( -- c-addr )"

  
sToNumberQ = do
  parsing "s>number?"
  effect "( c-addr n -- n flag flag )"


-- don't care:
-- unloop, variable, word, [char], recurse, r@, r>, quit, leave, find,
  -- exit, evaluate, environemnt?, abort, abort-quote, >r
-- vll??: ['], does>, variable, constant
  
-- coreWords :: [IO BuildState]
  -- add toNumber
  
coreWordsByIdentifier :: Script' (M.Map Parsable Word)
coreWordsByIdentifier = foldM addToList M.empty coreWords'
  where
  -- addToList :: M.Map Parsable (Word Semantics) -> Script' BuildState -> Script' (M.Map Parsable (Word Semantics))
  addToList :: M.Map Parsable Word -> Free WordDefinition () -> Script' (M.Map Parsable Word)
  addToList m b = do
      b' <- buildWord' b :: Script' BuildState
      let w' = view word b'
      return $ M.insert (view parsed w') w' m
  coreWords' = [sToNumberQ, pad, store, does, create, colon, semicolon, numberSign, numberSignGreater, numberSignS, bracketTick, tick, paren, star, starSlash, starSlashMod, plus, plusStore, plusLoop, comma, minus, TF.Words.dot, dotquote, slash, slashMod,zeroLess, zeroEquals, onePlus, oneMinus, twoStore, twoStar, if', then',twoSlash,twoFetch,twoDrop,twoDup,twoOver,twoSwap,lessThan,lessNumberSign,equals,greaterThan,toBody,toIn,toR, fetch, abort, abs', accept, align, aligned, allot, and', base, bl, cStore, cComma, cFetch, cellPlus, cells, TF.Words.char, charPlus, chars, constant, count, cr, decimal, TF.Words.depth, drop, dup, emit , execute, exit, find, fill, fmMod, here, hold, i, invert, j, key, leave, lshift, mStar, TF.Words.max, TF.Words.min, TF.Words.mod, move, TF.Words.negate, TF.Words.or, TF.Words.over, quit, rFrom, rFetch, recurse, rot, rShift, sQuote, do', loop, postpone, else', immediate', begin, until, swap, leftBracket, literal, sToD, sign, smslashrem, source, space, spaces, TF.Words.state, type', uDot, uLessThan, umStar, umMod, questionDup, toNumber]

