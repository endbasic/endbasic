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

' This benchmarking scenario combines loops, arrays, calls, branches, and
' string operations to approximate a more mixed and realistic workload.

DIM SHARED values(256) AS INTEGER

SUB fill(round%)
    FOR i% = 0 TO 255 STEP 1
        values(i%) = (i% * 9 + round% * 5) MOD 8191
    NEXT
END SUB

FUNCTION score%(x%, y%)
    SELECT CASE y% MOD 3
        CASE 0
            score% = (x% * 3 + y%) MOD 4093
        CASE 1
            score% = (x% * 5 + y% * 2) MOD 4093
        CASE ELSE
            score% = (x% * 7 + y% * 3) MOD 4093
    END SELECT
END FUNCTION

text$ = "thequickbrownfoxjumpsoveralazydog0123456789"
total% = 0
FOR round% = 1 TO 46900 STEP 1
    fill round%
    FOR i% = 0 TO 255 STEP 1
        total% = (total% + score%(values(i%), i%)) MOD 1000003
        IF (i% MOD 4) = 0 THEN
            piece$ = MID$(text$, (i% MOD 20) + 1, 4)
            total% = (total% + LEN%(piece$) + ASC%(LEFT$(piece$, 1))) MOD 1000003
        END IF
    NEXT
NEXT

PRINT total%
