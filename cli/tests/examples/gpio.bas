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

GPIO_MOCK_INJECT 8, TRUE
GPIO_MOCK_INJECT 8, TRUE
GPIO_MOCK_INJECT 8, FALSE

RUN

PRINT "Dumping GPIO trace..."
PRINT GPIO_MOCK_TRACE$

DISASM
