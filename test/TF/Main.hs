{-# LANGUAGE MultiWayIf, LambdaCase, OverloadedStrings #-}
module TF.Main where

import           Control.Error
import           Control.Lens
import           Control.Monad
import           Control.Monad.Trans.Class

import           Data.Functor
import           TF.ForthTypes as FT
import qualified Data.Map                     as M
import           Data.String
import Data.List (isInfixOf)
import           Lens.Family.Total            hiding ((&))
import           Test.Hspec                   hiding (after, before)
import           Test.Hspec.Expectations.Lens
import           Test.Hspec.Lens              hiding (after, before)
import           Test.QuickCheck
import           TF.CallChecker               (runChecker, runChecker', checkFile)
import           TF.Types                     as Types
import           TF.Util
import           TF.WordsBuilder (parsing, effect)
import qualified Data.Set as S
import TF.Errors

_ParseState = _2
_Success = _Right
_Failure = _Left

-- defChecker = ParseConfig {}
--     & allowMultipleEffects         .~ False
--     & allowLocalFailure            .~ False
--     & allCoreDynamic               .~ False
--     & allowDynamicInStackComments  .~ False
--     & allowCasts                   .~ False
--     & allowForcedEffects           .~ False
--     & subtypes                     .~ (const [])
--     & allowOOP                     .~ False
--     & thirdParty                   .~ []
  
checker1 = ParseConfig {}
    & typeCheck                    .~ True
    & topLevelEmpty                .~ True
    & readFromStream               .~ True
    & allowLocalFailure            .~ True
    & allCoreDynamic               .~ True
    & allowForcedEffects           .~ True
    & allowMultipleEffects         .~ True
    & thirdParty                   .~ [do { parsing "random";
                                            effect "( n -- n )" }]
    & allowCasts                   .~ False
    & allowOOP                     .~ False
    & allowDynamicInStackComments  .~ False
    & subtypes                     .~ (const [])

checker2 = checker1
    & allowMultipleEffects         .~ False
    & allCoreDynamic               .~ False
    & allowCasts                   .~ True

checker3 = checker2
    & allowMultipleEffects         .~ True

checker4 = checker2
   & allowCasts                    .~ False
   & subtypes .~ (\x ->
                   if | x == flag -> [ n ]
                      | True         -> [ ])


    

exampleConf :: ParseConfig
exampleConf = ParseConfig {}
                & typeCheck .~ True
                & readFromStream .~ True
                & topLevelEmpty .~ False

                & allowMultipleEffects .~ True
                & allowLocalFailure .~ True
                & allCoreDynamic .~ False
                & allowDynamicInStackComments .~ False
                & allowCasts .~ True
                & allowForcedEffects .~ True
                & subtypes .~ (const [])
                & allowOOP .~ True
                & thirdParty .~ [do { parsing "random"; effect "( n -- n )" }]

defTestConfig :: ParseConfig
defTestConfig = ParseConfig {}
                & typeCheck .~ True
                & readFromStream .~ True
                & topLevelEmpty .~ False

                & allowMultipleEffects .~ True
                & allowLocalFailure .~ False
                & allCoreDynamic .~ False
                & allowDynamicInStackComments .~ False
                & allowCasts .~ False
                & allowForcedEffects .~ False
                & subtypes .~ (const [])
                & allowOOP .~ False
                & thirdParty .~ []


check' conf = fst . runChecker' conf


forbidMultipleEffs = do
  let check = check' (defTestConfig & allowMultipleEffects .~ False)
  it "type clashes on a colon definition with multiple effects" $
    check ": foo + ;" `shouldHave` (_Failure._TypeClashM._MultiEffs)
  it "type clashes on an if-else expression with two effects" $
    check ": foo if 3 else bl then ;" `shouldHave` (_Failure._Clash)
  it "type checks an if-else expression with one effect" $
    check ": foo if 3 else 9 then ;" `shouldHave` _Success
  it "type checks an if expression with 'no' effect" $
    check ": foo if then ;" `shouldHave` _Success
  it "type clashes on an if expression with a nonempty effect" $
    check ": foo if 3 then ;" `shouldHave` _Failure
  
                
dynamic = do
  context "with allCoreDynamic set to True" $ do
    let check = check' (defTestConfig & allCoreDynamic .~ True)

    it "type checks a simple, dynamically correct composition" $ 
      check ": foo 3 4 + if 4 then ;" `shouldHave` _Success

    it "all types are dynamic in the effect of the addition word" $ do
      let result = check "+"
      result `shouldHave` (_Success._2.effects._Wrapped._1.traverse._2.before.traverse._1.only Dynamic)
      result `shouldHave` (_Success._2.effects._Wrapped._1.traverse._2.after.traverse._1.only Dynamic)
    context "and allowDynamicInStackComments set to False" $ do
      let check = check' (defTestConfig & allCoreDynamic .~ True & allowDynamicInStackComments .~ False)
      it "type clashes on using dyn in a stack comment" $
        check ": foo ( dyn -- dyn ) 3 + ;" `shouldHave` _Failure
    context "and allowDynamicInStackComments set to True" $ do
      let check = check' (defTestConfig & allCoreDynamic .~ True & allowDynamicInStackComments .~ False)
      it "type checks using dyn in a stack comment" $
        check ": foo ( dyn -- dyn ) 3 + ;" `shouldHave` _Failure
  context "with allowDynamicInStackComments set to True" $ do
    let check = check' (defTestConfig & allowDynamicInStackComments .~ True)
    it "type checks a matching all-dynamic stack comment" $
      check ": foo ( dyn dyn -- dyn ) + ;" `shouldHave` _Success
    it "type checks a matching semi-dynamic stack comment" $
      check ": foo ( dyn n -- dyn ) + ;" `shouldHave` _Success
    it "type clashes an incorrect semi-dynamic stack comment" $
      check ": foo ( dyn n -- u ) + ;" `shouldHave` _Failure
    
      

simpleStackCalculus = do
  let check = fst . runChecker' defTestConfig

  it "A single top-level, known word type checks" $

      check "#>" `shouldHave` _Right

  it "A valid top-level composition type checks" $

      check "#> 3" `shouldHave` _Right

  it "An invalid top-level composition type clashes" $
      check "3 #>" `shouldHave` (_Left._TypeClash)

allowLocalFailureFeature = do
  let check = fst . runChecker' (defTestConfig & allowLocalFailure .~ True)

  context "Given an invalid word definition:" $ do
    it "type checks a program where that word is not used" $
        check ": foo bl + ;" `shouldHave`  _Success
    it "creates a dictionary entry for that word" $ do
        check ": foo 3 0= + ;" `shouldHave` (_Success._2.definedWords'.at "foo"._Just._ColonDefinition._2._Failed)

    it "type clashes on using that word top-level" $
        check ": foo 4 0= + ; 9 foo" `shouldHave` (_Failure._ErrorT._ClashInWord)
    it "using that word in another word definition results in the correct FAILED reason" $ do
        let prog = ": foo 0 0= + ; : bar foo ;"
        check prog `shouldHave` (_Success._2.definedWords'.at "bar"._Just._ColonDefinition._2._Failed.filtered (\x -> "foo" `isInfixOf` x))

simpleColonDefinition = do
  let check = fst . runChecker' defTestConfig

      getColonDefEffects w program =
        ((preview (_Right._2.definedWords'.at w._Just._ColonDefinition._2._Checked._1) (check program)) :: Maybe [StackEffect])
      effectsOfColonDefinition = _ColonDefinition._2._Checked._1

      name = "myword"
      simpleColonDefinition = ": " ++ name ++ " 3 4 + ;"

  it "has no parse erros" $

      check simpleColonDefinition `shouldHave` _Success

  it "has made a new dictionary entry" $ do
    check simpleColonDefinition `shouldHave` (_Success._ParseState.definedWords'.at name._Just.effectsOfColonDefinition)

  it "has compiled a single stack effect" $ do
    check simpleColonDefinition `shouldHave` (_Success._ParseState.definedWords'.at name._Just.effectsOfColonDefinition.to length.only 1)

  it "has compiled the correct stack effect" $ do
    let effect = (getColonDefEffects name simpleColonDefinition) ^?! (_Just._head)

    let afterStack = effect ^. after

    effect ^. before `shouldBe` []
    effect ^. streamArgs `shouldBe` []
    length afterStack `shouldBe` 1

    let topOfAfterStack = afterStack ^?! _head & fst

    let isntReference :: DataType -> Bool
        isntReference x = case x of
                            Wildcard -> False
                            NoReference _ -> True
                            _ -> False

    topOfAfterStack `shouldSatisfy` isntReference

    case topOfAfterStack of
      NoReference x -> x ^?! (_PrimType.symbol) `shouldBe` FT.N

  it "has compiled the correct stack effect 2" $ do
    let effect' = getColonDefEffects "foo" ": foo dup 3 + ;"

    effect' `shouldHave` _Just._head.before._head._1._NoReference._PrimType.filtered (views symbol (== N))
    effect' `shouldHave` _Just._head.after._head._1._NoReference._PrimType.filtered (views symbol (== N))

colonDefStackComment = do
  let check = fst . runChecker' (defTestConfig & allowForcedEffects .~ True)

  it "succeeds type checking a correct effect" $ 
     check ": myfunc ( u1 u2 -- u3 ) + ;" `shouldHave` _Success

  it "type clashes on a wrong effect" $ 
      check ": myfunc ( u1 -- u2 ) + ;" `shouldHave` _Failure._TypeClash._NotMatchingStackComment

  it "you can force a wrong effect" $ 
      check ": myfunc ( u1 -!- u2 ) + ;" `shouldHave` _Success
  
oopFeature = do 
  let check = fst . runChecker' (defTestConfig & allowOOP .~ True)
  context "inferring the type of a field" $
    it "infers N when its used in the context of addition" $ 

      check  "object class var text end-class button button new text @ 4 +"`shouldHave` (_Success._2.classFields.at "button"._Just.traverse.filtered (\(x,_) -> x == "text")._2._InferredByField.after._head._1._Reference._NoReference._PrimType.only FT.n)
  it "taking the type from the class definition" $ 
  
      check "object class var text ( *char ) end-class button"`shouldHave` (_Success._2.classFields.at "button"._Just.traverse.filtered (\(x,_) -> x == "text")._2._ByFieldDefinition.after._head._1._Reference._NoReference._PrimType.only FT.char)

  context "deriving classes" $
    context "fields are derived" $ do
      it "when the field type was defined in the superclass definition" $ 
        check  "object class var size ( *n ) end-class button button class end-class subbutton" `shouldHave` (_Success._2.classFields.at "subbutton"._Just.traverse.filtered (\(x,_) -> x == "size")._2._ByFieldDefinition.after._head._1._Reference._NoReference._PrimType.only FT.n)

      it "when the field type was inferred" $ 
        check "object class var size end-class button button class end-class subbutton button new size @ 2 +" `shouldHave` (_Success._2.classFields.at "subbutton"._Just.traverse.filtered (\(x,_) -> x == "size")._2._InferredByField.after._head._1._Reference._NoReference._PrimType.only FT.n)

  context "checking method implementations" $ do
    context "favours the forced effect specified on class definition" $ do
      it "when the method implementation does not type check" $ do
        let result = check "object class var text method init ( -!- n n ) end-class button :noname 9 0= + ; button defines init"
        result `shouldHave` _Right
      it "when the method implementation has a different inferred effect" $ do
        let result = check "object class var text method init ( -!- n n ) end-class button :noname + ; button defines init"
        result `shouldHave` _Right
    it "there is an error when the method implementation and the class definition have both a stack comment" $ do
        let result = check "object class var text method init ( n -- n ) end-class button :noname ( n -- n ) + ; button defines init"
        result `shouldHave` (_Left._ErrorO._DefinedTwice)
    context "when there is not a stack comment specified on class definition but on the method implementation" $ do
      it "succeeds when the inferred effect of the method implementation matches the stack comment" $ do
        let result = check "object class var text method init end-class button :noname ( button -- button n n ) 2 3 ; button defines init"
        result `shouldHave` _Right
      it "fails when the inferred effect of the method implementation does not match the stack comment" $ do
        let result = check "object class var text method init end-class button :noname ( -- n ) 2 3 ; button defines init"
        result `shouldHave` (_Left._ErrorO._OOPErrT._NotMatchingStackComment)


create = do
  let check = fst . runChecker' defTestConfig

      getColonDefEffects w program =
        ((preview (_Right._2.definedWords'.at w._Just._ColonDefinition._2._Checked._1) (check program)) :: Maybe [StackEffect]) ^?! _Just
      getCreateDefEffects w program =
        ((preview (_Right._2.definedWords'.at w._Just._CreateDefinition) (check program)) :: Maybe [StackEffect]) ^?! _Just
  it "when a colon definition's body contains 2 'create' the compiled effect contains two defining arguments" $ do
    let name = "myfunc"
        colonDef = ": myfunc create create ;"
        effects = getColonDefEffects name colonDef

    let getDefiningArgs = _head.streamArgs.traverse._Defining
        args = (toListOf getDefiningArgs effects) :: [DefiningArg]


    effects `shouldHave` _head.streamArgs.traverse._Defining
    length args `shouldBe` 2

  context "when the compiled effect of a word demands two stream arguments of different types" $
    context "the word applied to two stream arguments type checks" $ do
      let colonDef = ": myfunc create 0 , create bl , ; myfunc " ++ name1 ++ " " ++ name2
          name1 = "foo"
          name2 = "bar"

      it "type checks" $ do

        check colonDef `shouldHave` _Success

      it "creates two words referencing the correct types" $ do
        let effects1 = getCreateDefEffects name1 colonDef
            effects2 = getCreateDefEffects name2 colonDef

        effects1 `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.symbol.filtered (== FT.N)
        effects2 `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.symbol.filtered (== FT.Char)
  context "when a create-word has a does> part which sets the cell type" $ do
    it "where the create does not have a comma and constraints the type" $ do
      let prog =  ": foo create does> @ 4 + ; foo bla"
          bla = getCreateDefEffects "bla" prog
      bla `shouldHave` _head.after._head._1._NoReference._PrimType.symbol.only N

      let foo = getColonDefEffects "foo" prog
      foo `shouldHave` _head.streamArgs._head._Defining.runtimeEffect._Just._head._1.after._head._1._NoReference._PrimType.symbol.only N
    it "where the type is constrained by a later comma" $ do
      let prog = ": foo create does> @ + ; : bla foo 4 , ; bla bar"
          bar = getCreateDefEffects "bar" prog
      bar `shouldHave` _head.before._head._1._NoReference._PrimType.symbol.only N
      bar `shouldHave` _head.after._head._1._NoReference._PrimType.symbol.only N

    it "where the create does not have a comma and does not constrain the type" $ do
      let prog =  ": foo create does> dup ; foo bla"
          bla = getCreateDefEffects "bla" prog
      bla `shouldHave` _head.after.traverse._1._Reference._UnknownType

  context "when there is a create-comma" $ do
    it "the resulting word has an unknown type" $ do
      let prog = ": foo create , ; foo bla"
          bla = getCreateDefEffects "bla" prog
      bla `shouldHave` _head.after._head._1._Reference._UnknownType
    it "and the resulting word's type is constrained with store" $ do
      let prog = ": foo create , ; foo bla 3 bla !"
          bla = getCreateDefEffects "bla" prog
      bla `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.symbol.only N
    it "and the resulting word's type was constrained by comma outside the initial create" $ do
      let prog = "9 : foo create , ; foo bla 3 bla !"
          bla = getCreateDefEffects "bla" prog
      bla `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.symbol.only N
    it "and the resulting word's type was constrained by comma inside the initial create" $ do
      let prog = ": foo create 7 , ; foo bla 3 bla !"
          bla = getCreateDefEffects "bla" prog
      bla `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.symbol.only N
    it "the does> effect constrains the effect" $ do
      let prog = ": foo create , does> @ + ; 9 foo bla foo bar"
          bla = getCreateDefEffects "bla" prog
      bla `shouldHave` _head.before._head._1._NoReference._PrimType.symbol.only N
      bla `shouldHave` _head.after._head._1._NoReference._PrimType.symbol.only N
      let bar = getCreateDefEffects "bar" prog
      bar `shouldHave` _head.before._head._1._NoReference._PrimType.symbol.only U
      bar `shouldHave` _head.after._head._1._NoReference._PrimType.symbol.only U
      bar `shouldHave` element 1.before._head._1._NoReference._PrimType.symbol.only N
      bar `shouldHave` element 1.after._head._1._NoReference._PrimType.symbol.only N

    it "and the resulting word's type was constrained by comma outside the initial create and later a wrong type gets stored in it" $ do
      check "9 : foo create , ; foo bla 8 0= bla !" `shouldHave` (_Failure._Clash)

  context "when the compiled effect of a word demands a stream argument" $ do
    it "a wrong word stack effect is rejected" $ do
      check ": foo ( x D'name':[ n ] -- ) create , ;" `shouldHave` (_Failure._NotMatchingStackComment)
    it "a correct stack effect is approved" $ do
      check ": foo ( n D'name':[ n ] -- ) create , ;" `shouldHave` _Success
    let name = "myfunc"
        colonDef = ": myfunc create ;"
    context "when the created word is of unknown type" $ do
      it "the dictionary entry's effect contains exactly a stream argument" $ do
        let effects = getColonDefEffects name colonDef

        effects `shouldHave` traverse.streamArgs._head
        effects `shouldNotHave` traverse.streamArgs._tail._head
    it "using that word creates a new dictionary entry with an after stack containing a reference to an unknown type" $ do
      let name = "blub"
          colonDef = ": myfunc create ; myfunc " ++ name
          effects = getCreateDefEffects name colonDef

      -- length effects `shouldBe` 1
      effects `shouldHave` to length.only 1
      effects `shouldHave` _head.after._head._1._Reference._UnknownType
    it "and that unknown type depends on a wildcard argument, the resulting definition has the correct type when the wildcard is unified with a certain type" $ do
      let colonDef = ": foo create dup , ; bl foo " ++ name
          name = "asd"
          effects = getCreateDefEffects name colonDef
      -- length effects `shouldBe` 1
      effects `shouldHave` to length.only 1
      effects `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.filtered (views symbol (== Char))


    context "when the created word is of known type" $ do
      it "there is a dictionary entry with exactly that type for that name 1" $ do
          let name = "blub"
              colonDef = ": myfunc create ; myfunc " ++ name ++ " 0 ,"

              effects = getCreateDefEffects name colonDef

          -- length effects `shouldBe` 1
          effects `shouldHave` to length.only 1
          effects `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.filtered (views symbol (== N))
      it "there is a dictionary entry with exactly that type for that name 2" $ do
          let name = "blub"
              colonDef = ": myfunc create 0 , ; myfunc " ++ name

          let effects = getCreateDefEffects name colonDef

          -- length effects `shouldBe` 1
          effects `shouldHave` to length.only 1
          effects `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.filtered (views symbol (== N))
      it "the dictionary entry's effect contains exactly one stream argument" $ do
          let name = "myfunc"
              colonDef = ": myfunc create 0 , ;"
              effects = getColonDefEffects name colonDef


          effects `shouldHave` traverse.streamArgs._head
          effects `shouldNotHave` traverse.streamArgs._tail._head
    context "which is a defining argument" $
        it "the dictionary entry's effect contains a defining stream argument and no other stream argument" $ do
            let effects = getColonDefEffects name colonDef
            effects `shouldHave` traverse.streamArgs.traverse._Defining
            effects `shouldNotHave` traverse.streamArgs.traverse._NotDefining
    context "given a top level create expression" $ do
      let name = "hi"
      context "which provides type information" $ do
         it "creates a dictionary entry with the correct type" $ do
            let program = "create " ++ name ++ " 0 4 ,"
                effects = getCreateDefEffects name program
            effects `shouldHave` to length.only 1
            effects `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.filtered (views symbol (== N))
         context "and the value of that type was put on the stack before 'create'" $
           it "creates a dictionary entry with the correct type" $ do
                let program = "bl create " ++ name ++ " ,"
                let effects = getCreateDefEffects name program
                effects `shouldHave` to length.only 1
                effects `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.filtered (views symbol (== Char))
         it "there is a error if a value of incorrect type is attempted to be written into that reference" $ do
           let program = "create foo 4 , 9 0= foo !"
           check program `shouldHave` (_Failure._Clash)

      context "which provides no type information" $ do
         it "creates a dictionary entry with a unknowntype reference" $ do
            let program = "create " ++ name
                effects = getCreateDefEffects name program
            effects `shouldHave` to length.only 1
            effects `shouldHave` _head.after._head._1._Reference._UnknownType
         it "type checks dereferencing that word" $ do
            let program = "create " ++ name ++ " " ++ name ++ " @"
            check program `shouldHave` _Success
         it "storing a value afterwards sets the reference value of that variable" $ do
            let program = "create foo 3 foo !"
                effects = getCreateDefEffects "foo" program
            effects `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.filtered (views symbol (== N))
         it "reading from that variable and using that value of unknown in such a way that the type gets known, sets the referenced type of the variable" $ do
            let program = "create foo foo @ 3 +"
                effects = getCreateDefEffects "foo" program
            effects `shouldHave` _head.after._head._1._Reference._NoReference._PrimType.filtered (views symbol (== N))
    it "inferring a reference to a reference of known type works" $ do
      let name = "bar"
          program = "create foo 3 , create " ++ name ++ " " ++ name ++ " @ @ 3 +"
          effects = getCreateDefEffects name program
      effects `shouldHave` _head.after._head._1._Reference._Reference._NoReference._PrimType.filtered (views symbol (== N))
    context "inferring a reference to a reference of unknown type works" $ do

        it "when one reference is stored in another" $ do
          let ref1 = "bar"
              ref2 = "foo"
              program = "create " ++ ref2 ++ " create " ++ ref1 ++ " " ++ ref2 ++ " " ++ ref1 ++ " !"
          let ref1effs = getCreateDefEffects ref1 program
              ref2effs = getCreateDefEffects ref2 program
          let unknownType1 = ref1effs ^? _head.after._head._1._Reference._Reference._UnknownType
          let unknownType2 = ref2effs ^? _head.after._head._1._Reference._UnknownType

          unknownType1 `shouldBe` unknownType2
        it "when one reference is stored in another and one of the reference types is later inferred to a concrete type" $ do
          let ref1 = "bar"
              ref2 = "foo"
              program = "create " ++ ref2 ++ " create " ++ ref1 ++ " " ++ ref2 ++ " " ++ ref1 ++ " ! " ++ ref2 ++ " @ 3 +"
          let ref1effs = getCreateDefEffects ref1 program
              ref2effs = getCreateDefEffects ref2 program
          let knownType1 = ref1effs ^? _head.after._head._1._Reference._Reference._NoReference
          let knownType2 = ref2effs ^? _head.after._head._1._Reference._NoReference

          knownType1 `shouldBe` knownType2

assertions = do
  let check = fst . runChecker' (defTestConfig & allowLocalFailure .~ True)

      getColonDefEffects w program =
        ((preview (_Right._2.definedWords'.at w._Just._ColonDefinition._2._Checked._1) (check program)) :: Maybe [StackEffect]) ^?! _Just
      getCreateDefEffects w program =
        ((preview (_Right._2.definedWords'.at w._Just._CreateDefinition) (check program)) :: Maybe [StackEffect]) ^?! _Just
  it "throws an error failure" $ do
    let program = ": foo 2 3 ( Assert xt ) + ;"
        result = fst $ runChecker' (defTestConfig & allowLocalFailure .~ False) program
    result `shouldHave` (_Failure._TypeClash)

  it "validates correct assertions for the top part of the stack" $ do
    check   ": foo 2 3 ( Assert n ) + ;" `shouldHave` (_Success._2.definedWords'.at "foo"._Just._ColonDefinition._2._Checked._1)

  it "rejects incorrect forced assertion which does not mention whole stack" $ do
    check   ": foo 2 3 ( Assert! n ) + ;"  `shouldHave` (_Success._2.definedWords'.at "foo"._Just._ColonDefinition._2._Failed)

  it "rejects incorrect forced assertion which mentions more than is on the stack" $ do
    check   ": foo 3 ( Assert! n n ) + ;"  `shouldHave` (_Success._2.definedWords'.at "foo"._Just._ColonDefinition._2._Failed)

  it "validates correct assertions" $ do
    check   ": foo 2 3 ( Assert n n ) + ;" `shouldHave` (_Success._2.definedWords'.at "foo"._Just._ColonDefinition._2._Checked._1)

  context "in a tick construct" $ do
    context "which is executed" $ do
      it "and pretty simple" $
        check ": foo ( n n -- n ) + ; ' foo" `shouldHave` _Success
      it "correctly asserting the xd resulting from tick" $ do
        check ": foo ( n n -- n ) + ; ' foo ( Assert xt:[ n n -- n ] )" `shouldHave` _Success
      it "correctly rejecting a wrong assertion with respect to the xd resulting from tick" $ do
        check ": foo ( n n -- n ) + ; ' foo ( Assert xt:[ n xd -- n ] )" `shouldHave` (_Failure._Clash)
    context "which is compiled" $ do
      it "with no word stack comment" $ do
        check  ": foo ; : bla foo ( 'addition':[ n n -- n ] -- ) ' ;"  `shouldHave` (_Success._2.definedWords'.at "bla"._Just._ColonDefinition._2._Checked._1)
      it "with a word stack stack comment" $ do
        check   ": bla ( 'addition':[ n n -- n ] -- xt:[ n n -- n ] ) ( 'addition':[ n n -- n ] -- ) ' ;" `shouldHave` (_Success._2.definedWords'.at "bla"._Just._ColonDefinition._2._Checked._1)

  context "in an execute construct" $ do
    it "which is compiled" $ do
      check  ": foo ; : bla foo ( Assert xt:[ n n -- n ] ) execute ;"  `shouldHave` (_Success._2.definedWords'.at "bla"._Just._ColonDefinition._2._Checked._1)  
  

immediate = do
  let check = fst . runChecker' defTestConfig
      getColonDefEffects w program =
        ((preview (_Right._2.definedWords'.at w._Just._ColonDefinition._2._Checked._1) (check program)) :: Maybe [StackEffect])
  it "postponing an immediate word just undoes the immediate nature" $ do
      let program = ": foo + ; immediate : bla postpone foo ;"
          effects1 :: Maybe [StackEffect]
          effects1 = getColonDefEffects "foo" program :: Maybe [StackEffect]
          effects2 = getColonDefEffects "bla" program :: Maybe [StackEffect]
      effects1 `shouldHave` _Just

      -- effects1 `shouldBe` effects2
  it "postponing a non-immediate word in the definition of an immediate word" $ do
      let program = ": foo + ; : bla postpone foo ; immediate : bar bla ;"
      let effects1 = getColonDefEffects "foo" program
          effects2 = getColonDefEffects "bar" program

      effects1 `shouldBe` effects2

subtyping = do
  let check = fst . runChecker' (defTestConfig & subtypes .~ getSubtypes)
  it "top level" $
    check "4 bl +" `shouldHave` _Right
  it "as a reference is a subtype of another if the referenced value is a subtype of the other referenced value" $
    check "create foo 4 , create bar bl , bl foo !" `shouldHave` _Right
  

main :: IO ()
main = hspec $
  describe "runChecker'" $ do
    let check = fst . runChecker' defTestConfig
        getCreateDefEffects w program = ((preview (_Right._2.definedWords'.at w._Just._CreateDefinition) (check program)) :: Maybe [StackEffect]) ^?! _Just
        getColonDefEffects w program =
          ((preview (_Right._2.definedWords'.at w._Just._ColonDefinition._2._Checked._1) (check program)) :: Maybe [StackEffect])


    describe "Allow failure of colon definition type checking if it is not used:" $
      allowLocalFailureFeature

    context "Checking simple stack calculus" $
      simpleStackCalculus

    context "When provided with a valid colon definition" $
      simpleColonDefinition


    context "when a word definition has a defined stack effect comment" $ do
      colonDefStackComment

    context "when provided with an if expression in a word definition" $ do
      let name = "myfunc"
          colonDef = ": myfunc 3 0< if 4 2 + then ;"
      it "compiles 2 stack effects" $ do
          let effects = getColonDefEffects name colonDef

          effects `shouldHave` _Just.to length.only 2

    immediate

    context "handling defining stream arguments" $
      create

    it "type checking fails when an immediate word leaves something on the stack at compile time" $ do
       let program = ": foo + ; immediate : bar [ 3 2 ] foo ;"
       check program `shouldHave` (_Failure._UnemptyStack)
    it "type checking fails when an immediate word demands that there must be something on the stack at compile time" $ do
       let program = ": foo + ; immediate : bar foo ;"
       check program `shouldHave` (_Failure._UnemptyStack)

    it "type checks using a word in a colon def which had been created before at compile time" $ do
       let program = ": myword [ create bla 3 , ] bla ;"
       check program `shouldHave` _Success


    it "parses an xt with effect in stack effect" $
          check  ": foo ( xt:[ -- ] -- ) drop ;" `shouldHave` _Right
    it "parses an xt without effect in stack effect" $
          check  ": foo ( xt -- ) drop ;" `shouldHave` _Right
    it "parses an xt without effect in stack effect and clashes on not matching stack comment" $
          check  ": foo ( xt -- ) + ;" `shouldHave` (_Left._TypeClash._NotMatchingStackComment)

    context "type checks subtyping" $ do
      subtyping

    it "given a colon definition with 'literal' in it, the compiled effect is correct" $ do
      let name = "foo"
          colonDef = ": " ++ name ++ " [ bl ] literal ;"
          effects = getColonDefEffects name colonDef
      effects `shouldHave` _Just._head.after._head._1._NoReference._PrimType.symbol.filtered (== FT.Char)

    context "OOP Features" $
      oopFeature
    
    context "respects assertions" $ do
      assertions

    context "Handles casts" cast

    context "Handles the dynamic features:" dynamic


cast = do
  let check = fst . runChecker' defTestConfig
      checkWithCasts = fst . runChecker' (defTestConfig & allowCasts .~ True)

  it "type checks a simple cast example" $ 
    checkWithCasts ": foo 2 ( cast n -- flag ) if 4 then ;" `shouldHave` _Success

  it "does not type check a simple cast example if casts are not allowed" $ 
    check ": foo 2 ( cast n -- flag ) if 4 then ;" `shouldHave` _Failure
