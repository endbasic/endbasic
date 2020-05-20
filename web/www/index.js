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
import * as xterm from "xterm";

var term = new xterm.Terminal();
term.setOption("fontSize", 20);
term.open(document.getElementById('terminal'));

var queue = [];
function readLine() {
    return new Promise(resolve => { queue.push(resolve); });
}

var interpreter = new endbasic_web.Interpreter(term, readLine);

var line = "";
term.onKey(e => {
    const printable = !e.domEvent.altKey && !e.domEvent.altGraphKey && !e.domEvent.ctrlKey
        && !e.domEvent.metaKey;

    if (e.domEvent.keyCode === 8) {
        if (line.length > 0) {
            term.write('\b \b');
            line = line.substring(0, line.length - 1);
        }
    } else if (e.domEvent.keyCode === 13) {
        term.write("\n\r");
        var resolveReadLine = queue.shift();
        resolveReadLine(line);
        line = "";
    } else if (printable) {
        term.write(e.key);
        line += e.key;
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
