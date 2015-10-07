include random.fs

create secret-number
create explain-wrong-guess

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

: success cr ." You guessed it! " cr
    \ ;
    \ ( assert n flag )
    swap drop ; 

: give-advice 
    cr ." The requested number is "
    0 < if ." larger. "
        else ." smaller. " then cr ;

' give-advice ( assert xt:[ n1 -- ] ) explain-wrong-guess !

: feedback ( n -- flag )
    secret-number @ -
    dup ( -- n n )

    0= dup ( -- n flag flag )
    if
        success ( -- flag )
       
    else
        \ give-advice ( -- flag )
        swap

        explain-wrong-guess @ ( assert xt:[ n1 -- ] ) execute

        ." Try again " cr
        
    then ;

\ bei success braucht es das swap drop -> beginuntil expr sollte fehler liefern!
\ bei worng-input ist stack effect comment notwendig
\ erst mit cast geht es oder mit n<flag
\ bei wrong-input braucht es das drop (lass ich wohl so)

: FALSE 1 0= ;

: wrong-input 
    drop
    ." Your input was not a number! " cr
    0 \ FALSE
    \ 1 0=
; 

: start-game 
    init-secret-number
    cr ." Guess the number between 0 and 99 " cr
    begin 
        read-guess 
        if feedback 
        else wrong-input
        then
    until ;
