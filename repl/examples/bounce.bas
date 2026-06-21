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

' Bounces colorful shapes around a boxed canvas to showcase graphics commands.

ON ERROR GOTO @error

DIM SHARED dots AS INTEGER
DIM SHARED filled AS BOOLEAN
DIM SHARED mode AS INTEGER
DIM SHARED radius AS INTEGER
DIM SHARED small AS BOOLEAN
DIM SHARED x1 AS INTEGER
DIM SHARED x2 AS INTEGER
DIM SHARED y1 AS INTEGER
DIM SHARED y2 AS INTEGER

DIM SHARED pos(10000, 2) AS INTEGER
DIM SHARED vel(10000, 2) AS INTEGER

FUNCTION random_velocity%
    DO
        random_velocity = 5 - RND() * 10.0
    LOOP WHILE random_velocity = 0
END FUNCTION

SUB init_dot(i%)
    pos(i, 0) = x1 + radius + RND() * (x2 - x1 - radius * 2)
    pos(i, 1) = y1 + radius + RND() * (y2 - y1 - radius * 2)
    vel(i, 0) = random_velocity
    vel(i, 1) = random_velocity
END SUB

SUB move_dot(i%)
    min_x = x1 + radius
    max_x = x2 - radius
    min_y = y1 + radius
    max_y = y2 - radius

    x = pos(i, 0) + vel(i, 0)
    IF x < min_x THEN
        x = min_x
        vel(i, 0) = -vel(i, 0)
    ELSEIF x > max_x THEN
        x = max_x
        vel(i, 0) = -vel(i, 0)
    END IF

    y = pos(i, 1) + vel(i, 1)
    IF y < min_y THEN
        y = min_y
        vel(i, 1) = -vel(i, 1)
    ELSEIF y > max_y THEN
        y = max_y
        vel(i, 1) = -vel(i, 1)
    END IF

    pos(i, 0) = x
    pos(i, 1) = y
END SUB

SUB reset_dots(new_count%)
    old_dots = dots
    dots = new_count
    IF dots < 10 THEN
        dots = 10
    ELSEIF dots > 10000 THEN
        dots = 10000
    END IF

    IF dots > old_dots THEN
        FOR i = old_dots TO dots - 1
            init_dot i
        NEXT
    END IF
END SUB

SUB configure_canvas
    small = GFX_WIDTH < 240 OR GFX_HEIGHT < 180
    IF small THEN
        radius = 6
        x1 = 8
        y1 = 24
    ELSE
        radius = 10
        x1 = 120
        y1 = 12
    END IF
    x2 = GFX_WIDTH - 12
    y2 = GFX_HEIGHT - 12
END SUB

SUB draw_legend
    COLOR 13
    IF small THEN
        PRINT "ESC, +/-, F, 0-9"
    ELSE
        PRINT "EndBASIC"
        PRINT "BOUNCE.BAS"
        PRINT
        PRINT dots; "dots"
        PRINT
        PRINT "ESC Exit"
        PRINT "+/- Count"
        PRINT "F Fill"
        PRINT
        PRINT "0 Circle"
        PRINT "1 Point"
        PRINT "2 Line"
        PRINT "3 Triangle"
        PRINT "4 Square"
        PRINT "5 Pentagon"
        PRINT "6 Hexagon"
    END IF
END SUB

GFX_SYNC FALSE
configure_canvas
dots = 0
filled = TRUE
frame_delay = 1.0 / 60.0
mode = 4
next_frame = MONOTONIC
reset_dots 100

DO
    key$ = INKEY
    SELECT CASE key$
        CASE "ESC": EXIT DO
        CASE "+": reset_dots dots + 10
        CASE "-": reset_dots dots - 10
        CASE "f", "F": filled = NOT filled
        CASE "0": mode = 0
        CASE "1": mode = 1
        CASE "2": mode = 2
        CASE "3": mode = 3
        CASE "4": mode = 4
        CASE "5": mode = 5
        CASE "6": mode = 6
    END SELECT

    CLS
    draw_legend

    COLOR 236
    GFX_RECTF x1, y1, x2, y2
    COLOR 15
    GFX_RECT x1 - 1, y1 - 1, x2 + 1, y2 + 1

    FOR i = 0 TO dots - 1
        move_dot i
        COLOR (i * 7) MOD 255 + 1
        x = pos(i, 0)
        y = pos(i, 1)
        dx = vel(i, 0)
        dy = vel(i, 1)

        SELECT CASE mode
            CASE 0
                IF filled THEN
                    GFX_CIRCLEF x, y, radius
                ELSE
                    GFX_CIRCLE x, y, radius
                END IF
            CASE 1
                GFX_PIXEL x, y
            CASE 2
                GFX_LINE x - dx * 2, y - dy * 2, x + dx * 2, y + dy * 2
            CASE 3
                x3 = x + dx * 2
                y3 = y + dy * 2
                x4 = x - dy * 2
                y4 = y + dx * 2
                x5 = x + dy * 2
                y5 = y - dx * 2
                IF filled THEN
                    GFX_TRIF x3, y3, x4, y4, x5, y5
                ELSE
                    GFX_TRI x3, y3, x4, y4, x5, y5
                END IF
            CASE 4
                IF filled THEN
                    GFX_RECTF x - radius, y - radius, x + radius, y + radius
                ELSE
                    GFX_RECT x - radius, y - radius, x + radius, y + radius
                END IF
            CASE 5
                px1 = x
                py1 = y - radius
                px2 = x + radius
                py2 = y - radius / 3
                px3 = x + (radius * 2) / 3
                py3 = y + radius
                px4 = x - (radius * 2) / 3
                py4 = y + radius
                px5 = x - radius
                py5 = y - radius / 3
                IF filled THEN
                    GFX_POLYF px1, py1, px2, py2, px3, py3, px4, py4, px5, py5
                ELSE
                    GFX_POLY px1, py1, px2, py2, px3, py3, px4, py4, px5, py5
                END IF
            CASE 6
                px1 = x - radius / 2
                py1 = y - radius
                px2 = x + radius / 2
                py2 = y - radius
                px3 = x + radius
                py3 = y
                px4 = x + radius / 2
                py4 = y + radius
                px5 = x - radius / 2
                py5 = y + radius
                px6 = x - radius
                py6 = y
                IF filled THEN
                    GFX_POLYF px1, py1, px2, py2, px3, py3, px4, py4, px5, py5, px6, py6
                ELSE
                    GFX_POLY px1, py1, px2, py2, px3, py3, px4, py4, px5, py5, px6, py6
                END IF
        END SELECT
    NEXT

    GFX_SYNC
    next_frame = next_frame + frame_delay
    delay = next_frame - MONOTONIC
    IF delay > 0 THEN
        SLEEP delay
    ELSE
        next_frame = MONOTONIC
    END IF
LOOP

COLOR
GFX_SYNC TRUE
CLS
END

@error
COLOR
CLS
IF ERRMSG = "No graphics support in this console" THEN
    PRINT ERRMSG
ELSE
    PRINT "ERROR: "; ERRMSG
END IF
END 1
