' EndBASIC
' Copyright 2022 Julio Merino
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

' Dumps all help messages for validation purposes.
'
' The interactive help messages are built into the interpreter as multiline
' raw strings and it is too easy to make mistakes when typing them (especially
' around line boundaries).  This dump serves to sanity-check that formatting
' works as intended.

PRINT "Output from HELP:"
HELP

DO
    READ topic$
    IF topic$ = "__DONE__" THEN EXIT DO
    PRINT "Output from HELP \""; topic$; "\":"
    HELP topic$
LOOP

' Help topics.
DATA "ARRAY"
DATA "CLOUD"
DATA "CONSOLE"
DATA "DATA"
DATA "FILE SYSTEM"
DATA "GRAPHICS"
DATA "HARDWARE"
DATA "INTERPRETER"
DATA "LANG"
DATA "NUMERICAL"
DATA "STORED"
DATA "STRING"

' Language reference.
DATA "ASSIGNMENTS"
DATA "ERROR HANDLING"
DATA "EXPRESSIONS"
DATA "FLOW CONTROL"
DATA "MISCELLANEOUS"
DATA "SYMBOLS"

' Commands.
DATA "CD"
DATA "CLEAR"
DATA "CLS"
DATA "COLOR"
DATA "DEG"
DATA "DIR"
DATA "EDIT"
DATA "GFX_CIRCLE"
DATA "GFX_CIRCLEF"
DATA "GFX_LINE"
DATA "GFX_PIXEL"
DATA "GFX_RECT"
DATA "GFX_RECTF"
DATA "GFX_SYNC"
DATA "GPIO_CLEAR"
DATA "GPIO_SETUP"
DATA "GPIO_WRITE"
DATA "HELP"
DATA "INPUT"
DATA "KILL"
DATA "LIST"
DATA "LOAD"
DATA "LOCATE"
DATA "LOGIN"
DATA "LOGOUT"
DATA "MOUNT"
DATA "NEW"
DATA "PRINT"
DATA "PWD"
DATA "RAD"
DATA "RANDOMIZE"
DATA "READ"
DATA "RESTORE"
DATA "RUN"
DATA "SAVE"
DATA "SHARE"
DATA "SIGNUP"
DATA "SLEEP"
DATA "UNMOUNT"

' Functions.
DATA "ASC"
DATA "ATN"
DATA "CHR"
DATA "CINT"
DATA "COS"
DATA "ERRMSG"
DATA "GFX_HEIGHT"
DATA "GFX_WIDTH"
DATA "GPIO_READ"
DATA "INKEY"
DATA "INT%"
DATA "LBOUND"
DATA "LEFT"
DATA "LEN"
DATA "LTRIM"
DATA "MAX"
DATA "MID"
DATA "MIN"
DATA "PI"
DATA "RIGHT"
DATA "RND"
DATA "RTRIM"
DATA "SCRCOLS"
DATA "SCRROWS"
DATA "SIN"
DATA "SQR"
DATA "STR$"
DATA "TAN"
DATA "UBOUND"

' End of data marker.
DATA "__DONE__"
