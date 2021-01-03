' EndBASIC
' Copyright 2020 Julio Merino
'
' Licensed under the Apache License, Version 2.0 (the "License"); you may not
' use this file except in compliance with the License.  You may obtain a copy
' of the License at:
'
'     http://www.apache.org/licenses/LICENSE-2.0
'
' Unless required by applicable law or agreed to in writing, software
' distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
' WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
' License for the specific language governing permissions and limitations
' under the License.

fg% = 15 ' Bright white.
bg% = 4 ' Blue.
title% = 14 ' Cyan.
bad% = 9 ' Bright red.
good% = 10 ' Bright green.

COLOR fg%, bg%
CLS
PRINT
COLOR title%, bg%
PRINT " Guess the number!"
PRINT "==================="
COLOR fg%, bg%
PRINT
INPUT "What's the largest number I can use"; max_num%
INPUT "How many attempts each time"; max_attempts%

wins% = 0
losses% = 0

again? = TRUE
WHILE again?
    PRINT
    secret% = DTOI%(RND#(1) * ITOD#(max_num%))
    PRINT "Alright! I have a secret number between 0 and"; max_num%

    attempts% = max_attempts%
    guess% = -1
    WHILE attempts% > 0 AND guess% <> secret%
        PRINT
        PRINT "You have"; attempts%; "attempts left to guess my number"
        INPUT "What's your guess"; guess%
        IF guess% <> secret% THEN
            COLOR bad%, bg%
            IF guess% < secret% THEN
                PRINT "Wrong."; guess%; "is too low!"
            ELSE
                PRINT "Wrong."; guess%; "is too high!"
            END IF
            COLOR fg%, bg%
        END IF
        attempts% = attempts% - 1
    END WHILE

    IF guess% = secret% THEN
        wins% = wins% + 1
        COLOR good%, bg%
        PRINT "Correct. You win! :-)"
    ELSE
        losses% = losses% + 1
        COLOR bad%, bg%
        PRINT "Sorry. You lost :-( The secret number was"; secret%
    END IF
    COLOR fg%, bg%
    PRINT

    INPUT "Do you want to play again"; again?
END WHILE

COLOR
CLS
PRINT "Score:"; wins%; "wins and"; losses%; "losses"
PRINT
PRINT "Thanks for playing"
PRINT
