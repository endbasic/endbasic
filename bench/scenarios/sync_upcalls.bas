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

' This benchmarking scenario performs many trigonometric builtin calls to
' exercise synchronous upcalls from the interpreter into native routines.

acc% = 0
FOR i% = 1 TO 26700000 STEP 1
    x# = i% / 1000
    acc% = (acc% + INT%(SIN#(x#) * 1000 + COS#(x#) * 1000)) MOD 1000003
NEXT

PRINT acc%
