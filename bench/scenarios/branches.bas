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

' This benchmarking scenario drives both IF and SELECT CASE decisions in a
' tight loop to exercise branch dispatch and control-flow handling.

score% = 0
FOR i% = 1 TO 24500000 STEP 1
    bucket% = i% MOD 10
    IF bucket% < 3 THEN
        score% = score% + 1
    ELSEIF bucket% < 7 THEN
        score% = score% + 2
    ELSE
        score% = score% + 3
    END IF

    SELECT CASE bucket%
        CASE 0, 1
            score% = score% + 5
        CASE 2 TO 4
            score% = score% + 7
        CASE IS < 8
            score% = score% + 11
        CASE ELSE
            score% = score% + 13
    END SELECT
NEXT

PRINT score%
