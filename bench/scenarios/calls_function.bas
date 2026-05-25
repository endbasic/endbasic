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

' This benchmarking scenario repeatedly invokes a small user-defined
' function to exercise function-call setup, return, and argument passing.

FUNCTION mix%(a%, b%)
    mix% = (a% * b% + (a% MOD 17) + (b% * 3)) MOD 4093
END FUNCTION

acc% = 0
FOR i% = 1 TO 26400000 STEP 1
    acc% = (acc% + mix%(i%, 9)) MOD 1000003
NEXT

PRINT acc%
