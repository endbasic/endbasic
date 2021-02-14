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

button = 8
led = 18

CLS
COLOR 11
PRINT
PRINT " GPIO demo"
PRINT "==========="
COLOR
PRINT
PRINT "This demo showcases how to poll a hardware button attached to a GPIO"
PRINT "pin and how to flash an LED attached to another one."
PRINT
COLOR 2
PRINT "To get started, follow these steps:"
COLOR
PRINT
PRINT "1. Connect an LED to pin"; led; "and to ground; don't forget to add a"
PRINT "   resistor inline."
PRINT
PRINT "2. Connect a push button to pin"; button; "and to ground.  We'll be"
PRINT "   using the built-in pull-up resistor for the input pin so there is"
PRINT "   no need to do any extra wiring."
PRINT
COLOR 1
PRINT "This demo is only functional on the Raspberry Pi and assumes you have"
PRINT "built EndBASIC with --features=rpi.  If these conditions are not met,"
PRINT "the demo will fail to run."
COLOR
PRINT
INPUT "Press ENTER when you are ready or CTRL+C to exit the demo...", dummy$

CLS
COLOR 11
PRINT
PRINT " GPIO demo"
PRINT "==========="
COLOR
PRINT

' Start by configuring the GPIO pins in the right modes.
GPIO_SETUP button, "IN-PULL-UP"
GPIO_SETUP led, "OUT"

' Now poll for a button press.  Note that we wait until the line value goes
' low because we enabled the built-in pull-*up* resistor.
PRINT "Waiting for a button press on pin"; button; "..."
WHILE GPIO_READ(button)
    SLEEP 0.05
WEND

' The button was pressed, so now flash the LED a bunch of times.
PRINT "Button pressed! Blinking LED on pin"; led; "..."
FOR i = 5 TO 1 STEP -1
    GPIO_WRITE led, TRUE
    SLEEP 0.1
    GPIO_WRITE led, FALSE
    SLEEP 0.1
    PRINT i
NEXT
