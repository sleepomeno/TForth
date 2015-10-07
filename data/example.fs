include random.fs

variable secret-number

: create-random-nr 101 random ;

: init-seed utime drop here xor utime drop lshift seed ! ;
: init-secret-number
    init-seed
    create-random-nr
    secret-number ! ;

: read-guess ( -- n flag )
    ." Guess the number between 0 and 100 " cr
    pad 2 accept
    pad swap 
    s>number?
    swap drop ;

: feedback ( n -- flag )
    secret-number @ - 
    dup ( -- n n )

    0= dup ( -- n flag flag )
    if
        ." You guessed it! You win! " cr
        ( -- n flag )
        swap drop \ forgetting this verschmutzt den stack
        ( -- flag )
    else
        ." Try again " cr
        swap ( -- flag n )
        ." Difference is: " . cr
        \ drop -1
        
    then ;

: start-game 
    init-secret-number

    begin
        read-guess 

        if 
            feedback
        else
            ." Your input was not a number! " cr
            drop
            0 
        then

    until

    ;


