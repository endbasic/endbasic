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

var UA = navigator.userAgent;
var isMobile = (
    /\b(BlackBerry|webOS|iPhone|IEMobile)\b/i.test(UA) ||
    /\b(Android|Windows Phone|iPad|iPod)\b/i.test(UA) ||
    (/\b(Macintosh)\b/i.test(UA) && 'ontouchend' in document)  // For iPad Pro.
);
var isAndroid = /\bAndroid\b/i.test(UA);

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
// We only do this on the desktop because mobile browsers will change the size every time they
// show the on-screen keyboard and that's not what we really want here.
if (!isMobile) {
    window.onresize = function() {
        let label = document.getElementById('terminal-size');
        label.innerText = "SIZE CHANGED; MUST RELOAD PAGE";
    };
}

var wt = new endbasic_web.WebTerminal(terminal, __SERVICE_URL__);

var osk = wt.on_screen_keyboard();
var mobileInput = document.getElementById('mobile-input');
if (isMobile) {
    $('#button-esc').on('click', function() {
        osk.press_escape();
        mobileInput.focus();
    });
    $('#button-up').on('click', function() {
        osk.press_arrow_up();
        mobileInput.focus();
    });
    $('#button-down').on('click', function() {
        osk.press_arrow_down();
        mobileInput.focus();
    });
    $('#button-left').on('click', function() {
        osk.press_arrow_left();
        mobileInput.focus();
    });
    $('#button-right').on('click', function() {
        osk.press_arrow_right();
        mobileInput.focus();
    });

    $('#controls').css('visibility', 'visible');

    if (isAndroid) {
        // Handling the keyboard on Android is messy.  If we have a real keyboard, we get keydown
        // events as we expect.  But if we have a soft keyboard, the keydown events are always
        // "empty".  Fortunately, we can use the input event to get data from the soft keyboard.
        // Unfortunately, we can have both real and soft keyboards on the same device, which means
        // we have to deal with possibly-duplicate events.  And to make things worse, even if we
        // just have a soft keyboard, some events (like Enter) come in only as keydown while others
        // (like letter presses) come in as both keydown and input.
        //
        // To cope with these cases, we install handlers for both keydown and input, but we only
        // recognize one of them within a short time period to avoid duplicate input.  This is quite
        // a hack that I'm sure has deficiencies, so restrict its use to Android.
        //
        // https://stackoverflow.com/questions/30743490/capture-keys-typed-on-android-virtual-keyboard-using-javascript

        var ignoreLastInput = false;
        mobileInput.addEventListener("input", function(key) {
            mobileInput.value = "";
            if (!ignoreLastInput && key.data != '') {
                osk.inject_input_event(key);
                ignoreLastInput = true;
                setTimeout(function() { ignoreLastInput = false; }, 5);
                key.preventDefault();
            }
        });
        mobileInput.addEventListener("keydown", function(key) {
            mobileInput.value = "";
            if (!ignoreLastInput && key.keyCode != 229) {
                osk.inject_keyboard_event(key);
                ignoreLastInput = true;
                setTimeout(function() { ignoreLastInput = false; }, 5);
                key.preventDefault();
            }
        });
    } else {
        mobileInput.addEventListener("keydown", function(key) {
            mobileInput.value = "";
            osk.inject_keyboard_event(key);
            key.preventDefault();
        });
    }
    terminal.addEventListener("click", function() {
        mobileInput.focus();
    });
    mobileInput.focus();
} else {
    mobileInput.hidden = true;
    window.addEventListener("keydown", function(key) {
        osk.inject_keyboard_event(key);
        key.preventDefault();
    });
    terminal.focus();
}

var sizeInChars = wt.size_description();
$('#terminal-size').text(sizeInChars);

wt.run_repl_loop();
