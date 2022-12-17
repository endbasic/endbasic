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

'
' Renders the full color palette.
'

CLS
row = 0
col = 0
FOR c = 0 TO 255
    LOCATE col, row

    SELECT CASE c
        CASE 0, 16 TO 21, 232 TO 239: COLOR 15, c
        CASE ELSE: COLOR 0, c
    END SELECT

    SELECT CASE c
        CASE IS < 10: PRINT "  "; c;
        CASE IS < 100: PRINT " "; c;
        CASE ELSE: PRINT c;
    END SELECT

    col = col + 6
    IF col > SCRCOLS - 5 THEN
        col = 0
        row = row + 1
    END IF
NEXT

COLOR
PRINT
