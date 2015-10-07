include random.fs

\ : variable ( D'name':[ n ] -- ) create ;
\ : variable create ;

\ : random ( n -!- n ) ;

\ : s>number? ( c-addr n -!- n flag flag ) ;

variable secret-number
variable explain-wrong-guess

: say-difference ( n -- )
    ." Difference is: "
    . cr ;

' say-difference ( a: xt:[ n -- ] ) explain-wrong-guess !


: create-random-nr 100 random ;

\ : init-seed ( -!- )
\     \ utime drop here xor utime drop lshift seed !
\ ;
: init-seed ( -!- ) utime drop here xor utime drop lshift seed ! ;

: init-secret-number
    init-seed
    create-random-nr
    secret-number ! ;
\ : init-secret-number ( -!- ) ;

: read-guess ( -- n flag )
    ." Guess the number between 0 and 99 " cr
    pad 2 accept
    pad swap 
    s>number?
    swap drop ;

: feedback 
    \ secret-number @ swap ( a: n )  -
    \ drop secret-number @ 8  -
    secret-number @ -
    dup ( -- n n )

    0= dup ( -- n flag flag )
    if
        ." You guessed it! You win! " cr
        \ ( a: n flag )
        swap drop \ forgetting this verschmutzt den stack
        \ ( a!: flag )
    else
        ." Try again " cr
        swap ( -- flag n )
        explain-wrong-guess @ ( a: xt:[ n -- ] ) execute
        \ drop
        
    then ;

: start-game 
    init-secret-number

    begin
        read-guess 

        cr .s cr

        dup
        if drop
            feedback
        else
            ." Your input was not a number! " cr
            swap drop
            \ 0 ( c: n -- flag ) 
        then

    until

    ;