include random.fs

create secret-number

: create-random-nr 100 random ;

: init-seed ( -!- ) utime drop here xor utime drop lshift seed ! ;

: init-secret-number
    init-seed
    create-random-nr
    secret-number ! ;

: read-guess 
    pad 2 accept
    pad swap 
    s>number?
    swap drop ;

: success cr ." You guessed it! " cr ;

: give-advice 
    swap 
    cr ." The requested number is "
    0 < if ." larger. "
        else ." smaller. " then cr ;

: feedback 
    secret-number @ -
    dup 

    0= dup 
    if
        success 
       
    else
        give-advice 

        ." Try again " cr
    then ;

: wrong-input 
    drop
    ." Your input was not a number! " cr
    0 ; 

: start-game 
    init-secret-number
    cr ." Guess the number between 0 and 99 " cr
    begin 
        read-guess 
        if feedback 
        else wrong-input
        then
    until ;