# Test: Out of global registers

## Source

```basic
DIM SHARED g000
DIM SHARED g001
DIM SHARED g002
DIM SHARED g003
DIM SHARED g004
DIM SHARED g005
DIM SHARED g006
DIM SHARED g007
DIM SHARED g008
DIM SHARED g009

DIM SHARED g010
DIM SHARED g011
DIM SHARED g012
DIM SHARED g013
DIM SHARED g014
DIM SHARED g015
DIM SHARED g016
DIM SHARED g017
DIM SHARED g018
DIM SHARED g019

DIM SHARED g020
DIM SHARED g021
DIM SHARED g022
DIM SHARED g023
DIM SHARED g024
DIM SHARED g025
DIM SHARED g026
DIM SHARED g027
DIM SHARED g028
DIM SHARED g029

DIM SHARED g030
DIM SHARED g031
DIM SHARED g032
DIM SHARED g033
DIM SHARED g034
DIM SHARED g035
DIM SHARED g036
DIM SHARED g037
DIM SHARED g038
DIM SHARED g039

DIM SHARED g040
DIM SHARED g041
DIM SHARED g042
DIM SHARED g043
DIM SHARED g044
DIM SHARED g045
DIM SHARED g046
DIM SHARED g047
DIM SHARED g048
DIM SHARED g049

DIM SHARED g050
DIM SHARED g051
DIM SHARED g052
DIM SHARED g053
DIM SHARED g054
DIM SHARED g055
DIM SHARED g056
DIM SHARED g057
DIM SHARED g058
DIM SHARED g059

DIM SHARED g060
DIM SHARED g061
DIM SHARED g062
DIM SHARED g063
DIM SHARED g064
DIM SHARED g065
DIM SHARED g066
DIM SHARED g067
DIM SHARED g068
DIM SHARED g069

DIM SHARED g070
DIM SHARED g071
DIM SHARED g072
DIM SHARED g073
DIM SHARED g074
DIM SHARED g075
DIM SHARED g076
DIM SHARED g077
DIM SHARED g078
DIM SHARED g079
```

## Compilation errors

```plain
71:12: Out of global registers
```

# Test: Out of local registers

## Source

```basic
l000 = 0
l001 = 0
l002 = 0
l003 = 0
l004 = 0
l005 = 0
l006 = 0
l007 = 0
l008 = 0
l009 = 0

l010 = 0
l011 = 0
l012 = 0
l013 = 0
l014 = 0
l015 = 0
l016 = 0
l017 = 0
l018 = 0
l019 = 0

l020 = 0
l021 = 0
l022 = 0
l023 = 0
l024 = 0
l025 = 0
l026 = 0
l027 = 0
l028 = 0
l029 = 0

l030 = 0
l031 = 0
l032 = 0
l033 = 0
l034 = 0
l035 = 0
l036 = 0
l037 = 0
l038 = 0
l039 = 0

l040 = 0
l041 = 0
l042 = 0
l043 = 0
l044 = 0
l045 = 0
l046 = 0
l047 = 0
l048 = 0
l049 = 0

l050 = 0
l051 = 0
l052 = 0
l053 = 0
l054 = 0
l055 = 0
l056 = 0
l057 = 0
l058 = 0
l059 = 0

l060 = 0
l061 = 0
l062 = 0
l063 = 0
l064 = 0
l065 = 0
l066 = 0
l067 = 0
l068 = 0
l069 = 0

l070 = 0
l071 = 0
l072 = 0
l073 = 0
l074 = 0
l075 = 0
l076 = 0
l077 = 0
l078 = 0
l079 = 0

l080 = 0
l081 = 0
l082 = 0
l083 = 0
l084 = 0
l085 = 0
l086 = 0
l087 = 0
l088 = 0
l089 = 0

l090 = 0
l091 = 0
l092 = 0
l093 = 0
l094 = 0
l095 = 0
l096 = 0
l097 = 0
l098 = 0
l099 = 0

l100 = 0
l101 = 0
l102 = 0
l103 = 0
l104 = 0
l105 = 0
l106 = 0
l107 = 0
l108 = 0
l109 = 0

l110 = 0
l111 = 0
l112 = 0
l113 = 0
l114 = 0
l115 = 0
l116 = 0
l117 = 0
l118 = 0
l119 = 0

l120 = 0
l121 = 0
l122 = 0
l123 = 0
l124 = 0
l125 = 0
l126 = 0
l127 = 0
l128 = 0
l129 = 0

l130 = 0
l131 = 0
l132 = 0
l133 = 0
l134 = 0
l135 = 0
l136 = 0
l137 = 0
l138 = 0
l139 = 0

l140 = 0
l141 = 0
l142 = 0
l143 = 0
l144 = 0
l145 = 0
l146 = 0
l147 = 0
l148 = 0
l149 = 0

l150 = 0
l151 = 0
l152 = 0
l153 = 0
l154 = 0
l155 = 0
l156 = 0
l157 = 0
l158 = 0
l159 = 0

l160 = 0
l161 = 0
l162 = 0
l163 = 0
l164 = 0
l165 = 0
l166 = 0
l167 = 0
l168 = 0
l169 = 0

l170 = 0
l171 = 0
l172 = 0
l173 = 0
l174 = 0
l175 = 0
l176 = 0
l177 = 0
l178 = 0
l179 = 0

l180 = 0
l181 = 0
l182 = 0
l183 = 0
l184 = 0
l185 = 0
l186 = 0
l187 = 0
l188 = 0
l189 = 0

l190 = 0
l191 = 0
l192 = 0
l193 = 0
l194 = 0
l195 = 0
l196 = 0
l197 = 0
l198 = 0
l199 = 0
```

## Compilation errors

```plain
212:1: Out of local registers
```

# Test: Out of temporary registers in final assignment

## Source

```basic
result = 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18 + 19 + 20 + 21 + 22 + 23 + 24 + 25 + 26 + 27 + 28 + 29 + 30 + 31 + 32 + 33 + 34 + 35 + 36 + 37 + 38 + 39 + 40 + 41 + 42 + 43 + 44 + 45 + 46 + 47 + 48 + 49 + 50 + 51 + 52 + 53 + 54 + 55 + 56 + 57 + 58 + 59 + 60 + 61 + 62 + 63 + 64 + 65 + 66 + 67 + 68 + 69 + 70 + 71 + 72 + 73 + 74 + 75 + 76 + 77 + 78 + 79 + 80 + 81 + 82 + 83 + 84 + 85 + 86 + 87 + 88 + 89 + 90 + 91 + 92 + 93 + 94 + 95 + 96 + 97 + 98 + 99 + 100 + 101 + 102 + 103 + 104 + 105 + 106 + 107 + 108 + 109 + 110 + 111 + 112 + 113 + 114 + 115 + 116 + 117 + 118 + 119 + 120 + 121 + 122 + 123 + 124 + 125 + 126 + 127 + 128 + 129 + 130 + 131 + 132 + 133 + 134 + 135 + 136 + 137 + 138 + 139 + 140 + 141 + 142 + 143 + 144 + 145 + 146 + 147 + 148 + 149 + 150 + 151 + 152 + 153 + 154 + 155 + 156 + 157 + 158 + 159 + 160 + 161 + 162 + 163 + 164 + 165 + 166 + 167 + 168 + 169 + 170 + 171 + 172 + 173 + 174 + 175 + 176 + 177 + 178 + 179 + 180 + 181 + 182 + 183 + 184 + 185 + 186 + 187 + 188 + 189 + 190 + 191
```

## Compilation errors

```plain
1:14: Out of temp registers
```

# Test: Out of temporary registers in expression evaluation

## Source

```basic
result = 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18 + 19 + 20 + 21 + 22 + 23 + 24 + 25 + 26 + 27 + 28 + 29 + 30 + 31 + 32 + 33 + 34 + 35 + 36 + 37 + 38 + 39 + 40 + 41 + 42 + 43 + 44 + 45 + 46 + 47 + 48 + 49 + 50 + 51 + 52 + 53 + 54 + 55 + 56 + 57 + 58 + 59 + 60 + 61 + 62 + 63 + 64 + 65 + 66 + 67 + 68 + 69 + 70 + 71 + 72 + 73 + 74 + 75 + 76 + 77 + 78 + 79 + 80 + 81 + 82 + 83 + 84 + 85 + 86 + 87 + 88 + 89 + 90 + 91 + 92 + 93 + 94 + 95 + 96 + 97 + 98 + 99 + 100 + 101 + 102 + 103 + 104 + 105 + 106 + 107 + 108 + 109 + 110 + 111 + 112 + 113 + 114 + 115 + 116 + 117 + 118 + 119 + 120 + 121 + 122 + 123 + 124 + 125 + 126 + 127 + 128 + 129 + 130 + 131 + 132 + 133 + 134 + 135 + 136 + 137 + 138 + 139 + 140 + 141 + 142 + 143 + 144 + 145 + 146 + 147 + 148 + 149 + 150 + 151 + 152 + 153 + 154 + 155 + 156 + 157 + 158 + 159 + 160 + 161 + 162 + 163 + 164 + 165 + 166 + 167 + 168 + 169 + 170 + 171 + 172 + 173 + 174 + 175 + 176 + 177 + 178 + 179 + 180 + 181 + 182 + 183 + 184 + 185 + 186 + 187 + 188 + 189 + 190 + 191 + 192
```

## Compilation errors

```plain
1:10: Out of temp registers
```
