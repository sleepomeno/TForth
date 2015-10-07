include random.fs

\ : variable ( D'name':[ n ] -- ) create ;
\ : variable create ;

\ : random ( n -!- n ) ;

\ : s>number? ( c-addr n -!- n flag flag ) ;

variable secret-number
variable explain-wrong-guess

: give-advice ( n -- )
    ." The requested number is "
    0 < if ." larger. "
        else ." smaller. " then cr ;

' give-advice ( assert: xt:[ n -- ] ) explain-wrong-guess !

: create-random-nr 100 random ;

: init-seed ( -!- ) utime drop here xor utime drop lshift seed ! ;

: init-secret-number
    init-seed
    create-random-nr
    secret-number ! ;
\ : init-secret-number ( -!- ) ;

: read-guess ( -- n flag )
    pad 2 accept
    pad swap 
    s>number?
    swap drop ;

: success ." You guessed it!" cr
        \ ( assert n flag )
        swap drop \ forgetting this verschmutzt den stack
        ; ( assert! flag ) ;

: feedback 
    \ secret-number @ swap ( a: n )  -
    \ drop secret-number @ 8  -
    secret-number @ -
    dup ( -- n n )

    0= dup ( -- n flag flag )
    if
        success
    else
        swap ( -- flag n )
        give-advice

        ." Try again " cr
        \ explain-wrong-guess @ ( assert xt:[ n -- ] ) execute
        \ drop
        
    then ;


: FALSE 1 0= ;

: wrong-input 
   ." Your input was not a number! " cr
    0 ; \ ( cast n -- flag ) ;

: start-game 
    init-secret-number
    ." Guess the number between 0 and 99 " cr
    begin
        read-guess 
        if feedback
        else wrong-input
        then
    until ;

 