' EndBASIC
' Copyright 2021 Julio Merino
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

' Runs the gpio.bas example using mock GPIO data to drive the program.

LOAD "DEMOS:/GPIO.BAS"

DIM __GPIO_MOCK_DATA(20) AS INTEGER
__GPIO_MOCK_DATA(2) = 811 ' Return high for pin 8 (button).
__GPIO_MOCK_DATA(3) = 811 ' Return high for pin 8 (button).
__GPIO_MOCK_DATA(4) = 810 ' Return low for pin 8 (button).
__GPIO_MOCK_LAST = 0

RUN

PRINT "Dumping GPIO trace..."
FOR i = 0 TO __GPIO_MOCK_LAST - 1
    PRINT "__GPIO_MOCK_DATA", i, __GPIO_MOCK_DATA(i)
NEXT
