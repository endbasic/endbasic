# EndBASIC
# Copyright 2021 Julio Merino
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may not
# use this file except in compliance with the License.  You may obtain a copy
# of the License at:
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
# License for the specific language governing permissions and limitations
# under the License.

Invoke-WebRequest `
    -Uri https://www.libsdl.org/release/SDL2-devel-2.26.1-VC.zip `
    -OutFile SDL2-devel-2.26.1-VC.zip
Invoke-WebRequest `
    -Uri https://www.libsdl.org/projects/SDL_ttf/release/SDL2_ttf-devel-2.0.15-VC.zip `
    -OutFile SDL2_ttf-devel-2.0.15-VC.zip

unzip SDL2-devel-2.26.1-VC.zip
unzip SDL2_ttf-devel-2.0.15-VC.zip

[void](New-Item -Force -Type Directory libs)
Copy-Item .\SDL2-2.26.1\lib\x64\*.lib,.\SDL2_ttf-2.0.15\lib\x64\*.lib libs
[void](New-Item -Force -Type Directory dlls)
Copy-Item .\SDL2-2.26.1\lib\x64\*.dll,.\SDL2_ttf-2.0.15\lib\x64\*.dll dlls
Copy-Item .\SDL2-2.26.1\lib\x64\*.txt,.\SDL2_ttf-2.0.15\lib\x64\*.txt dlls

Remove-Item -Recurse -Force .\SDL2-2.26.1,.\SDL2_ttf-2.0.15,SDL2*.zip

foreach ($dir in
    ".",
    "target",
    "target\debug", "target\debug\deps", "target\debug\examples",
    "target\release", "target\release\deps", "target\release\examples") {
    [void](New-Item -Force -Type Directory $dir)
    Write-Output "Copying SDL2 libs and dlls to $dir"
    Copy-Item dlls\* $dir
    Copy-Item libs\* $dir
}
