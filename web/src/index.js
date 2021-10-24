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

import * as endbasic_web from "endbasic_web";
import $ from "jquery";

var buildId = endbasic_web.get_build_id();
$('#build-id').text(buildId);

var template = "Build ID: " + buildId;
$('#report-issue').attr(
    "href", "https://github.com/endbasic/endbasic/issues/new?body=" + template);

let terminal = document.getElementById('terminal');

function fitTerminal() {
    let footer = document.getElementsByTagName('footer');
    terminal.style.margin = "15px";
    terminal.width = document.documentElement.clientWidth - 30;
    terminal.height = document.documentElement.clientHeight - footer[0].clientHeight - 30;
}
fitTerminal();

// TODO(jmmv): We should hook fitTerminal() into resize, but EndBASIC cannot react to console
// size changes.  Instead, invalidate the size as a warning...
window.onresize = function() {
    let label = document.getElementById('terminal-size');
    label.innerText = "SIZE CHANGED; MUST RELOAD PAGE";
};

var wt = new endbasic_web.WebTerminal(terminal);

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

var sizeInChars = wt.size_description();
$('#terminal-size').text(sizeInChars);

terminal.focus();
wt.run_repl_loop();
