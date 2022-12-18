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

mask = &x_0070
IF (&x_0050 AND mask) <> 0 THEN PRINT "Match 1"
IF (&x_0001 AND mask) <> 0 THEN PRINT "Match 2"

mask = &b10
IF (1 AND mask) <> 0 THEN PRINT "Match 3"
IF (2 AND mask) <> 0 THEN PRINT "Match 4"
IF (7 AND mask) <> 0 THEN PRINT "Match 5"

PRINT NOT 123456

PRINT 1 << 20
PRINT 128 >> 2
