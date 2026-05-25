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

' This benchmarking scenario repeatedly writes and reads a two-dimensional
' array to exercise indexed storage access inside nested loops.

DIM grid(40, 30) AS INTEGER

sum% = 0
FOR round% = 1 TO 22000 STEP 1
    row% = 0
    WHILE row% < 40
        col% = 0
        WHILE col% < 30
            grid(row%, col%) = (row% * 31 + col% * 17 + round%) MOD 8191
            col% = col% + 1
        WEND
        row% = row% + 1
    WEND
    row% = 0
    WHILE row% < 40
        col% = 0
        WHILE col% < 30
            sum% = (sum% + grid(row%, col%)) MOD 1000003
            col% = col% + 1
        WEND
        row% = row% + 1
    WEND
NEXT

PRINT sum%
