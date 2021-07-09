{-
pomeranian
-}

coprotocol S => Console =
    ConsolePut :: S => Get( [Char] | S) 
    ConsoleGet :: S => Put( [Char] | S) 
    ConsoleClose :: S => TopBot 


proc cheq  :: | A => A = 
    | ch0 => ch1 -> do
        ch0 |=| ch1

proc p0 :: | => Put([Char] | TopBot) =
    |  => ch -> do
        put "pomeranian" on ch
        halt ch

proc p1 :: | Console, Put([Char] | TopBot) =>  =
    | _console, ch => -> do
        get v on ch

        hput ConsolePut on _console
        put v on _console

        hput ConsoleClose on _console
        close _console

        halt ch 

proc run =
    | _console => ->  do
        plug
            p0(   |               => ch1)
            cheq( |  ch2          => ch3)
            cheq( |  ch1          => ch2)
            p1(   | _console, ch4 =>    )
            cheq( |  ch3          => ch4)
