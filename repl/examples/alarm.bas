' EndBASIC
' Copyright 2026 Julio Merino
'
' This program is free software: you can redistribute it and/or modify
' it under the terms of the GNU Affero General Public License as published by
' the Free Software Foundation, either version 3 of the License, or
' (at your option) any later version.
'
' This program is distributed in the hope that it will be useful,
' but WITHOUT ANY WARRANTY; without even the implied warranty of
' MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
' GNU Affero General Public License for more details.
'
' You should have received a copy of the GNU Affero General Public License
' along with this program.  If not, see <https://www.gnu.org/licenses/>.

' Cycles through rising and falling tones until a key is pressed.

PRINT "Press any key to stop..."

DO
    FOR pitch = 800 TO 1200 STEP 10
        SOUND pitch, 0.02
        IF INKEY <> "" THEN END
    NEXT

    FOR pitch = 1200 TO 800 STEP -10
        SOUND pitch, 0.02
        IF INKEY <> "" THEN END
    NEXT
LOOP
