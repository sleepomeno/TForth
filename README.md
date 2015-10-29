# TForth

## What is it?

**TForth** is a prototype for optional, pluggable typing for Forth.

## What is the checker able to check?

Basically, the prototype handles the majority of the words of the CORE wordset of Forth ANSI 94. More details can be found in [my thesis](http://www.ub.tuwien.ac.at/dipl/2015/AC12652979.pdf) 

## How do I build it?

First, you need the Haskell [stack](https://github.com/commercialhaskell/stack) build tool.
Then you can build the executable:

```
stack install
```

This installs the *TFCommandline* executable.

## How do I use it?

Look at the flag options:

```
TFCommandline --help
```

### Example
Suppose the file _myfile_ has the content
```
: add5 5 + ;
```

Call the checker:
```
TFCommandline --filename=myfile
```

### TODOs

* Add missing configuration options to commandline interface
* Add support for create>
* Add other wordsets
* ...
