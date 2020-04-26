' EndBASIC
' Copyright 2020 Julio Merino
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

' Tests that the scripting interface does not have interactive functionality.

' TODO(jmmv): We should have more tests here, but we cannot until the
' interpreter is able to continue execution after an error.

' Interactive help should not be available in scripts.
HELP
