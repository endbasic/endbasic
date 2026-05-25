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

' This benchmarking scenario polls for keyboard input while mixing in extra
' arithmetic work to measure the cost of frequent asynchronous upcalls.

total% = 0
FOR i% = 1 TO 16000000 STEP 1
    total% = (total% + LEN%(INKEY)) MOD 1000003
NEXT

acc% = 1
FOR i% = 1 TO 40000000 STEP 1
    acc% = (acc% * 17 + (i% MOD 97) + (i% / 3)) MOD 1000003
NEXT

total% = (total% + acc%) MOD 1000003

PRINT total%
