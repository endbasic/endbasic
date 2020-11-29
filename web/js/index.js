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

import * as endbasic_web from "../pkg/index.js";
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

var wt = new endbasic_web.WebTerminal();

var UA = navigator.userAgent;
var isMobile = (
    /\b(BlackBerry|webOS|iPhone|IEMobile)\b/i.test(UA) ||
    /\b(Android|Windows Phone|iPad|iPod)\b/i.test(UA)
);
if (isMobile) {
    var osk = wt.on_screen_keyboard();
    $('#button-esc').on('click', function() {
        osk.press_escape();
        term.focus();
    });
    $('#button-up').on('click', function() {
        osk.press_arrow_up();
        term.focus();
    });
    $('#button-down').on('click', function() {
        osk.press_arrow_down();
        term.focus();
    });
    $('#button-left').on('click', function() {
        osk.press_arrow_left();
        term.focus();
    });
    $('#button-right').on('click', function() {
        osk.press_arrow_right();
        term.focus();
    });

    $('#controls').css('visibility', 'visible');
}

term.focus();
wt.run_repl_loop(term);
