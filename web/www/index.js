// EndBASIC
// Copyright 2020 Julio Merino
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not
// use this file except in compliance with the License.  You may obtain a copy
// of the License at:
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.

import * as endbasic_web from "endbasic-web";
import $ from "jquery";
import * as xterm from "xterm";
import * as xterm_fit_addon from "xterm-addon-fit";

var buildId = endbasic_web.get_build_id();
$('#build-id').text(buildId);

var template = "Build ID: " + buildId;
$('#report-issue').attr(
    "href", "https://github.com/jmmv/endbasic/issues/new?body=" + template);

var term = new xterm.Terminal();
term.setOption("fontSize", 18);
const fitAddon = new xterm_fit_addon.FitAddon();
term.loadAddon(fitAddon);
term.open(document.getElementById('terminal'));
fitAddon.fit();

var queue = [];
function readLine() {
    return new Promise(resolve => { queue.push(resolve); });
}

var interpreter = new endbasic_web.Interpreter(term, readLine);

var line = "";
term.onData(e => {
    for (var i = 0; i < e.length; i++) {
        let ch = e.charAt(i);
        if (ch === "\x7f") {
            if (line.length > 0) {
                term.write('\b \b');
                line = line.substring(0, line.length - 1);
            }
        } else if (ch === "\x0d") {
            term.write("\n\r");
            var resolveReadLine = queue.shift();
            resolveReadLine(line);
            line = "";
        } else {
            term.write(ch);
            line += ch;
        }
    }
});

async function next(term, readLine, interpreter) {
    term.write("Ready\n\r");
    let line = await readLine();
    interpreter = await interpreter.run(line);
    let error = interpreter.last_error();
    if (error.length != 0) {
        term.write("ERROR: " + error + "\n\r");
    }
    setImmediate(next, term, readLine, interpreter);
}

next(term, readLine, interpreter);

term.focus();
