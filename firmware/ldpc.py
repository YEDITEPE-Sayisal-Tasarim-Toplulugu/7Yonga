
import math

bg1_shiftvals = [[-1 for _ in range(68)] for _ in range(46)]

bg2_shiftvals = [[-1 for _ in range(52)] for _ in range(42)]

bg2_shiftvals[0][0] = 9
bg2_shiftvals[0][1] = 117
bg2_shiftvals[0][2] = 204
bg2_shiftvals[0][3] = 26
bg2_shiftvals[0][6] = 189
bg2_shiftvals[0][9] = 205
bg2_shiftvals[0][10] = 0
bg2_shiftvals[0][11] = 0

bg2_shiftvals[1][0] = 167
bg2_shiftvals[1][3] = 166
bg2_shiftvals[1][4] = 253
bg2_shiftvals[1][5] = 125
bg2_shiftvals[1][6] = 226
bg2_shiftvals[1][7] = 156
bg2_shiftvals[1][8] = 224
bg2_shiftvals[1][9] = 252
bg2_shiftvals[1][11] = 0
bg2_shiftvals[1][12] = 0

bg2_shiftvals[2][0] = 81
bg2_shiftvals[2][1] = 114
bg2_shiftvals[2][3] = 44
bg2_shiftvals[2][4] = 52
bg2_shiftvals[2][8] = 240
bg2_shiftvals[2][10] = 1
bg2_shiftvals[2][12] = 0
bg2_shiftvals[2][13] = 0

bg2_shiftvals[3][1] = 8
bg2_shiftvals[3][2] = 58
bg2_shiftvals[3][4] = 158
bg2_shiftvals[3][5] = 104
bg2_shiftvals[3][6] = 209
bg2_shiftvals[3][7] = 54
bg2_shiftvals[3][8] = 18
bg2_shiftvals[3][9] = 128
bg2_shiftvals[3][10] = 0
bg2_shiftvals[3][13] = 0

bg2_shiftvals[4][0] = 179
bg2_shiftvals[4][1] = 214
bg2_shiftvals[4][11] = 71
bg2_shiftvals[4][14] = 0

bg2_shiftvals[5][0] = 231
bg2_shiftvals[5][1] = 41
bg2_shiftvals[5][5] = 194
bg2_shiftvals[5][7] = 159
bg2_shiftvals[5][11] = 103
bg2_shiftvals[5][15] = 0

bg2_shiftvals[6][0] = 155
bg2_shiftvals[6][5] = 228
bg2_shiftvals[6][7] = 45
bg2_shiftvals[6][9] = 28
bg2_shiftvals[6][11] = 158
bg2_shiftvals[6][16] = 0

bg2_shiftvals[7][1] = 129
bg2_shiftvals[7][5] = 147
bg2_shiftvals[7][7] = 140
bg2_shiftvals[7][11] = 3
bg2_shiftvals[7][13] = 116
bg2_shiftvals[7][17] = 0

bg2_shiftvals[8][0] = 142
bg2_shiftvals[8][1] = 94
bg2_shiftvals[8][12] = 230
bg2_shiftvals[8][18] = 0

bg2_shiftvals[9][1] = 203
bg2_shiftvals[9][8] = 205
bg2_shiftvals[9][10] = 61
bg2_shiftvals[9][11] = 247
bg2_shiftvals[9][19] = 0

bg2_shiftvals[10][0] = 11
bg2_shiftvals[10][1] = 185
bg2_shiftvals[10][6] = 0
bg2_shiftvals[10][7] = 117
bg2_shiftvals[10][20] = 0

bg2_shiftvals[11][0] = 11
bg2_shiftvals[11][7] = 236
bg2_shiftvals[11][9] = 210
bg2_shiftvals[11][13] = 56
bg2_shiftvals[11][21] = 0

bg2_shiftvals[12][1] = 63
bg2_shiftvals[12][3] = 111
bg2_shiftvals[12][11] = 14
bg2_shiftvals[12][22] = 0

bg2_shiftvals[13][0] = 83
bg2_shiftvals[13][1] = 2
bg2_shiftvals[13][8] = 38
bg2_shiftvals[13][13] = 222
bg2_shiftvals[13][23] = 0

bg2_shiftvals[14][1] = 115
bg2_shiftvals[14][6] = 145
bg2_shiftvals[14][11] = 3
bg2_shiftvals[14][13] = 232
bg2_shiftvals[14][24] = 0

bg2_shiftvals[15][0] = 51
bg2_shiftvals[15][10] = 175
bg2_shiftvals[15][11] = 213
bg2_shiftvals[15][25] = 0

bg2_shiftvals[16][1] = 203
bg2_shiftvals[16][9] = 142
bg2_shiftvals[16][11] = 8
bg2_shiftvals[16][12] = 242
bg2_shiftvals[16][26] = 0
bg2_shiftvals[17][1] = 254
bg2_shiftvals[17][5] = 124
bg2_shiftvals[17][11] = 114
bg2_shiftvals[17][12] = 64
bg2_shiftvals[17][27] = 0
bg2_shiftvals[18][0] = 220
bg2_shiftvals[18][6] = 194
bg2_shiftvals[18][7] = 50
bg2_shiftvals[18][28] = 0
bg2_shiftvals[19][0] = 87
bg2_shiftvals[19][1] = 20
bg2_shiftvals[19][10] = 185
bg2_shiftvals[19][29] = 0
bg2_shiftvals[20][1] = 26
bg2_shiftvals[20][4] = 105
bg2_shiftvals[20][11] = 29
bg2_shiftvals[20][30] = 0
bg2_shiftvals[21][0] = 76
bg2_shiftvals[21][8] = 42
bg2_shiftvals[21][13] = 210
bg2_shiftvals[21][31] = 0
bg2_shiftvals[22][1] = 222
bg2_shiftvals[22][2] = 63
bg2_shiftvals[22][32] = 0
bg2_shiftvals[23][0] = 23
bg2_shiftvals[23][3] = 235
bg2_shiftvals[23][5] = 238
bg2_shiftvals[23][33] = 0
bg2_shiftvals[24][1] = 46
bg2_shiftvals[24][2] = 139
bg2_shiftvals[24][9] = 8
bg2_shiftvals[24][34] = 0
bg2_shiftvals[25][0] = 228
bg2_shiftvals[25][5] = 156
bg2_shiftvals[25][35] = 0
bg2_shiftvals[26][2] = 29
bg2_shiftvals[26][7] = 143
bg2_shiftvals[26][12] = 160
bg2_shiftvals[26][13] = 122
bg2_shiftvals[26][36] = 0
bg2_shiftvals[27][0] = 8
bg2_shiftvals[27][6] = 151
bg2_shiftvals[27][37] = 0
bg2_shiftvals[28][1] = 98
bg2_shiftvals[28][2] = 101
bg2_shiftvals[28][5] = 135
bg2_shiftvals[28][38] = 0
bg2_shiftvals[29][0] = 18
bg2_shiftvals[29][4] = 28
bg2_shiftvals[29][39] = 0
bg2_shiftvals[30][2] = 71
bg2_shiftvals[30][5] = 240
bg2_shiftvals[30][7] = 9
bg2_shiftvals[30][9] = 84
bg2_shiftvals[30][40] = 0
bg2_shiftvals[31][1] = 106
bg2_shiftvals[31][13] = 1
bg2_shiftvals[31][41] = 0
bg2_shiftvals[32][0] = 242
bg2_shiftvals[32][5] = 44
bg2_shiftvals[32][12] = 166
bg2_shiftvals[32][42] = 0
bg2_shiftvals[33][2] = 132
bg2_shiftvals[33][7] = 164
bg2_shiftvals[33][10] = 235
bg2_shiftvals[33][43] = 0
bg2_shiftvals[34][0] = 147
bg2_shiftvals[34][12] = 85
bg2_shiftvals[34][13] = 36
bg2_shiftvals[34][44] = 0
bg2_shiftvals[35][1] = 57
bg2_shiftvals[35][5] = 40
bg2_shiftvals[35][11] = 63
bg2_shiftvals[35][45] = 0
bg2_shiftvals[36][0] = 140
bg2_shiftvals[36][2] = 38
bg2_shiftvals[36][7] = 154
bg2_shiftvals[36][46] = 0
bg2_shiftvals[37][10] = 219
bg2_shiftvals[37][13] = 151
bg2_shiftvals[37][47] = 0
bg2_shiftvals[38][1] = 31
bg2_shiftvals[38][5] = 66
bg2_shiftvals[38][11] = 38
bg2_shiftvals[38][48] = 0
bg2_shiftvals[39][0] = 239
bg2_shiftvals[39][7] = 172
bg2_shiftvals[39][12] = 34
bg2_shiftvals[39][49] = 0
bg2_shiftvals[40][2] = 0
bg2_shiftvals[40][10] = 75
bg2_shiftvals[40][13] = 120
bg2_shiftvals[40][50] = 0
bg2_shiftvals[41][1] = 129
bg2_shiftvals[41][5] = 229
bg2_shiftvals[41][11] = 118
bg2_shiftvals[41][51] = 0

bg1_shiftvals[15][1] = 96
bg1_shiftvals[15][10] = 65
bg1_shiftvals[15][13] = 63
bg1_shiftvals[15][18] = 75
bg1_shiftvals[15][25] = 179
bg1_shiftvals[15][37] = 0

bg1_shiftvals[16][1] = 64
bg1_shiftvals[16][3] = 49
bg1_shiftvals[16][11] = 49
bg1_shiftvals[16][20] = 51
bg1_shiftvals[16][22] = 154
bg1_shiftvals[16][38] = 0

bg1_shiftvals[17][0] = 7
bg1_shiftvals[17][14] = 164
bg1_shiftvals[17][16] = 59
bg1_shiftvals[17][17] = 1
bg1_shiftvals[17][21] = 144
bg1_shiftvals[17][39] = 0

bg1_shiftvals[18][1] = 42
bg1_shiftvals[18][12] = 233
bg1_shiftvals[18][13] = 8
bg1_shiftvals[18][18] = 155
bg1_shiftvals[18][19] = 147
bg1_shiftvals[18][40] = 0

bg1_shiftvals[19][0] = 60
bg1_shiftvals[19][1] = 73
bg1_shiftvals[19][7] = 72
bg1_shiftvals[19][8] = 127
bg1_shiftvals[19][10] = 224
bg1_shiftvals[19][41] = 0

bg1_shiftvals[20][0] = 151
bg1_shiftvals[20][3] = 186
bg1_shiftvals[20][9] = 217
bg1_shiftvals[20][11] = 47
bg1_shiftvals[20][22] = 160
bg1_shiftvals[20][42] = 0

bg1_shiftvals[21][1] = 249
bg1_shiftvals[21][5] = 121
bg1_shiftvals[21][16] = 109
bg1_shiftvals[21][20] = 131
bg1_shiftvals[21][21] = 171
bg1_shiftvals[21][43] = 0

bg1_shiftvals[22][0] = 64
bg1_shiftvals[22][12] = 142
bg1_shiftvals[22][13] = 188
bg1_shiftvals[22][17] = 158
bg1_shiftvals[22][44] = 0

bg1_shiftvals[23][1] = 156
bg1_shiftvals[23][2] = 147
bg1_shiftvals[23][10] = 170
bg1_shiftvals[23][18] = 152
bg1_shiftvals[23][45] = 0

bg1_shiftvals[24][0] = 112
bg1_shiftvals[24][3] = 86
bg1_shiftvals[24][4] = 236
bg1_shiftvals[24][11] = 116
bg1_shiftvals[24][22] = 222
bg1_shiftvals[24][46] = 0

bg1_shiftvals[25][1] = 23
bg1_shiftvals[25][6] = 136
bg1_shiftvals[25][7] = 116
bg1_shiftvals[25][14] = 182
bg1_shiftvals[25][47] = 0

bg1_shiftvals[26][0] = 195
bg1_shiftvals[26][2] = 243
bg1_shiftvals[26][4] = 215
bg1_shiftvals[26][15] = 61
bg1_shiftvals[26][48] = 0

bg1_shiftvals[27][1] = 25
bg1_shiftvals[27][6] = 104
bg1_shiftvals[27][8] = 194
bg1_shiftvals[27][49] = 0

bg1_shiftvals[28][0] = 128
bg1_shiftvals[28][4] = 165
bg1_shiftvals[28][19] = 181
bg1_shiftvals[28][21] = 63
bg1_shiftvals[28][50] = 0

bg1_shiftvals[29][1] = 86
bg1_shiftvals[29][14] = 236
bg1_shiftvals[29][18] = 84
bg1_shiftvals[29][25] = 6
bg1_shiftvals[29][51] = 0

bg1_shiftvals[30][0] = 216
bg1_shiftvals[30][10] = 73
bg1_shiftvals[30][13] = 120
bg1_shiftvals[30][24] = 9
bg1_shiftvals[30][52] = 0

bg1_shiftvals[31][1] = 95
bg1_shiftvals[31][7] = 177
bg1_shiftvals[31][22] = 172
bg1_shiftvals[31][25] = 61
bg1_shiftvals[31][53] = 0

bg1_shiftvals[32][0] = 221
bg1_shiftvals[32][12] = 1
bg1_shiftvals[32][14] = 1
bg1_shiftvals[32][24] = 1
bg1_shiftvals[32][54] = 1

bg1_shiftvals[33][1] = 1
bg1_shiftvals[33][2] = 1
bg1_shiftvals[33][11] = 1
bg1_shiftvals[33][21] = 1
bg1_shiftvals[33][55] = 1

bg1_shiftvals[34][0] = 1
bg1_shiftvals[34][7] = 1
bg1_shiftvals[34][15] = 1
bg1_shiftvals[34][17] = 1
bg1_shiftvals[34][56] = 1

bg1_shiftvals[35][1] = 1
bg1_shiftvals[35][6] = 1
bg1_shiftvals[35][12] = 1
bg1_shiftvals[35][22] = 1
bg1_shiftvals[35][57] = 1

bg1_shiftvals[36][0] = 1
bg1_shiftvals[36][14] = 1
bg1_shiftvals[36][15] = 1
bg1_shiftvals[36][18] = 1
bg1_shiftvals[36][58] = 1

bg1_shiftvals[37][1] = 1
bg1_shiftvals[37][13] = 1
bg1_shiftvals[37][23] = 1
bg1_shiftvals[37][59] = 1

bg1_shiftvals[38][0] = 1
bg1_shiftvals[38][9] = 1
bg1_shiftvals[38][10] = 1
bg1_shiftvals[38][12] = 1
bg1_shiftvals[38][60] = 1

bg1_shiftvals[39][1] = 1
bg1_shiftvals[39][3] = 1
bg1_shiftvals[39][7] = 1
bg1_shiftvals[39][19] = 1
bg1_shiftvals[39][61] = 1

bg1_shiftvals[40][0] = 1
bg1_shiftvals[40][8] = 1
bg1_shiftvals[40][17] = 1
bg1_shiftvals[40][62] = 1

bg1_shiftvals[41][1] = 1
bg1_shiftvals[41][3] = 1
bg1_shiftvals[41][9] = 1
bg1_shiftvals[41][18] = 1
bg1_shiftvals[41][63] = 1

bg1_shiftvals[42][0] = 1
bg1_shiftvals[42][4] = 1
bg1_shiftvals[42][24] = 1
bg1_shiftvals[42][64] = 1

bg1_shiftvals[43][1] = 1
bg1_shiftvals[43][16] = 1
bg1_shiftvals[43][18] = 1
bg1_shiftvals[43][25] = 1
bg1_shiftvals[43][65] = 1

bg1_shiftvals[44][0] = 1
bg1_shiftvals[44][7] = 1
bg1_shiftvals[44][9] = 1
bg1_shiftvals[44][22] = 1
bg1_shiftvals[44][66] = 1

bg1_shiftvals[45][1] = 1
bg1_shiftvals[45][6] = 1
bg1_shiftvals[45][10] = 1
bg1_shiftvals[45][67] = 1
bg1_shiftvals[0][0] = 250
bg1_shiftvals[0][1] = 69
bg1_shiftvals[0][2] = 226
bg1_shiftvals[0][3] = 159
bg1_shiftvals[0][5] = 100
bg1_shiftvals[0][6] = 10
bg1_shiftvals[0][9] = 59
bg1_shiftvals[0][10] = 229
bg1_shiftvals[0][11] = 110
bg1_shiftvals[0][12] = 191
bg1_shiftvals[0][13] = 9
bg1_shiftvals[0][15] = 195
bg1_shiftvals[0][16] = 23
bg1_shiftvals[0][18] = 190
bg1_shiftvals[0][19] = 35
bg1_shiftvals[0][20] = 239
bg1_shiftvals[0][21] = 31
bg1_shiftvals[0][22] = 1
bg1_shiftvals[0][23] = 0

bg1_shiftvals[1][0] = 2
bg1_shiftvals[1][2] = 239
bg1_shiftvals[1][3] = 117
bg1_shiftvals[1][4] = 124
bg1_shiftvals[1][5] = 71
bg1_shiftvals[1][7] = 222
bg1_shiftvals[1][8] = 104
bg1_shiftvals[1][9] = 173
bg1_shiftvals[1][11] = 220
bg1_shiftvals[1][12] = 102
bg1_shiftvals[1][14] = 109
bg1_shiftvals[1][15] = 132
bg1_shiftvals[1][16] = 142
bg1_shiftvals[1][17] = 155
bg1_shiftvals[1][19] = 255
bg1_shiftvals[1][21] = 28
bg1_shiftvals[1][22] = 0
bg1_shiftvals[1][23] = 0
bg1_shiftvals[1][24] = 0

bg1_shiftvals[2][0] = 106
bg1_shiftvals[2][1] = 111
bg1_shiftvals[2][2] = 185
bg1_shiftvals[2][4] = 63
bg1_shiftvals[2][5] = 117
bg1_shiftvals[2][6] = 93
bg1_shiftvals[2][7] = 229
bg1_shiftvals[2][8] = 177
bg1_shiftvals[2][9] = 95
bg1_shiftvals[2][10] = 39
bg1_shiftvals[2][13] = 142
bg1_shiftvals[2][14] = 225
bg1_shiftvals[2][15] = 225
bg1_shiftvals[2][17] = 245
bg1_shiftvals[2][18] = 205
bg1_shiftvals[2][19] = 251
bg1_shiftvals[2][20] = 117
bg1_shiftvals[2][24] = 0
bg1_shiftvals[2][25] = 0

bg1_shiftvals[3][0] = 121
bg1_shiftvals[3][1] = 89
bg1_shiftvals[3][3] = 84
bg1_shiftvals[3][4] = 20
bg1_shiftvals[3][6] = 150
bg1_shiftvals[3][7] = 131
bg1_shiftvals[3][8] = 243
bg1_shiftvals[3][10] = 136
bg1_shiftvals[3][11] = 86
bg1_shiftvals[3][12] = 246
bg1_shiftvals[3][13] = 219
bg1_shiftvals[3][14] = 211
bg1_shiftvals[3][16] = 240
bg1_shiftvals[3][17] = 76
bg1_shiftvals[3][18] = 244
bg1_shiftvals[3][20] = 144
bg1_shiftvals[3][21] = 12
bg1_shiftvals[3][22] = 1
bg1_shiftvals[3][25] = 0

bg1_shiftvals[4][0] = 157
bg1_shiftvals[4][1] = 102
bg1_shiftvals[4][26] = 0

bg1_shiftvals[5][0] = 205
bg1_shiftvals[5][1] = 236
bg1_shiftvals[5][3] = 194
bg1_shiftvals[5][12] = 231
bg1_shiftvals[5][16] = 28
bg1_shiftvals[5][21] = 123
bg1_shiftvals[5][22] = 115
bg1_shiftvals[5][27] = 0

bg1_shiftvals[6][0] = 183
bg1_shiftvals[6][6] = 22
bg1_shiftvals[6][10] = 28
bg1_shiftvals[6][11] = 67
bg1_shiftvals[6][13] = 244
bg1_shiftvals[6][17] = 11
bg1_shiftvals[6][18] = 157
bg1_shiftvals[6][20] = 211
bg1_shiftvals[6][28] = 0

bg1_shiftvals[7][0] = 220
bg1_shiftvals[7][1] = 44
bg1_shiftvals[7][4] = 159
bg1_shiftvals[7][7] = 31
bg1_shiftvals[7][8] = 167
bg1_shiftvals[7][14] = 104
bg1_shiftvals[7][29] = 0

bg1_shiftvals[8][0] = 112
bg1_shiftvals[8][1] = 4
bg1_shiftvals[8][3] = 7
bg1_shiftvals[8][12] = 211
bg1_shiftvals[8][16] = 102
bg1_shiftvals[8][19] = 164
bg1_shiftvals[8][21] = 109
bg1_shiftvals[8][22] = 241
bg1_shiftvals[8][24] = 90
bg1_shiftvals[8][30] = 0

bg1_shiftvals[9][0] = 103
bg1_shiftvals[9][1] = 182
bg1_shiftvals[9][10] = 109
bg1_shiftvals[9][11] = 21
bg1_shiftvals[9][13] = 142
bg1_shiftvals[9][17] = 14
bg1_shiftvals[9][18] = 61
bg1_shiftvals[9][20] = 216
bg1_shiftvals[9][31] = 0

bg1_shiftvals[10][1] = 98
bg1_shiftvals[10][2] = 149
bg1_shiftvals[10][4] = 167
bg1_shiftvals[10][7] = 160
bg1_shiftvals[10][8] = 49
bg1_shiftvals[10][14] = 58
bg1_shiftvals[10][32] = 0

bg1_shiftvals[11][0] = 77
bg1_shiftvals[11][1] = 41
bg1_shiftvals[11][12] = 83
bg1_shiftvals[11][16] = 182
bg1_shiftvals[11][21] = 78
bg1_shiftvals[11][22] = 252
bg1_shiftvals[11][23] = 22
bg1_shiftvals[11][33] = 0

bg1_shiftvals[12][0] = 160
bg1_shiftvals[12][1] = 42
bg1_shiftvals[12][10] = 21
bg1_shiftvals[12][11] = 32
bg1_shiftvals[12][13] = 234
bg1_shiftvals[12][18] = 7
bg1_shiftvals[12][34] = 0

bg1_shiftvals[13][0] = 177
bg1_shiftvals[13][3] = 248
bg1_shiftvals[13][7] = 151
bg1_shiftvals[13][20] = 185
bg1_shiftvals[13][23] = 62
bg1_shiftvals[13][35] = 0

bg1_shiftvals[14][0] = 206
bg1_shiftvals[14][12] = 55
bg1_shiftvals[14][15] = 206
bg1_shiftvals[14][16] = 127
bg1_shiftvals[14][17] = 16
bg1_shiftvals[14][21] = 229
bg1_shiftvals[14][36] = 0

bg1_shiftvals[15][0] = 40


# Set endeksi arrayi (her satır bir set, içerik verilen değerler)
set_indices = [
    [2, 4, 8, 16],
    [3, 6, 12, 24],
    [5, 10, 20, 40],
    [7, 14, 28],
    [9, 18, 36],
    [11, 22, 44],
    [13, 26],
    [15, 30]
]





infobits_in     = []
code_rates_bg2  = [float(10/52),float(10/14)]
code_rates_bg1  = [float(22/68),float(22/26)]
coderate        = 0.0
basegraph       = 0
bg1_size        = (46,68)
bg2_size        = (42,52)
Zc              = 0


def pad_infobits(infobits, Zc):
    K = len(infobits)
    target_len = 22 * Zc
    if K < target_len:
        padded = infobits + [0] * (target_len - K)
        return padded
    return infobits

# CRC beklenmiyor, A = K kabul edildi, 
def calculate_basegraph(infobits_len):
    if (infobits_len <= 292) or (infobits_len <= 3824 and coderate <= 0.67) or coderate <= 0.25:
        return 2
    else:
        return 1

def calculate_Zc(infobits_len):
    global Zc
    div_val = math.ceil(infobits_len / 22)
    print(div_val)
    for i in range(len(set_indices)):
        for j in range(len(set_indices[i])):
            if div_val == set_indices[i][j]:
                Zc = set_indices[i][j]
                break
            elif set_indices[i][j-1] < div_val < set_indices[i][j]:
                Zc = set_indices[i][j]
                break

def shift_identity(Zc):
    identity = [[0 for _ in range(Zc)] for _ in range(Zc)]
    for i in range(Zc):
        identity[i][i] = 1
    for i in range(Zc):
        for j in range(Zc):
            if identity[i][j] == 1:
                if j == Zc - 1:
                    identity[i][0] = 1
                    identity[i][j] = 0
                else:
                    identity[i][j + 1] = 1
                    identity[i][j] = 0
    return identity

def expand_basegraph(basegraph, Zc):
    if basegraph == 1:
        shiftvals = bg1_shiftvals
        rows, cols = bg1_size
        expanded_matrix = [[0 for _ in range(cols * Zc)] for _ in range(rows * Zc)]

        # O
        for i in range(4):
            for j in range(26, 68):
                for row in range(Zc):
                    for column in range(Zc):
                        expanded_matrix[i * Zc + row][j * Zc + column] = 0

        # I
        for i in range(4, 46):
            for j in range(26, 68):
                val = bg1_shiftvals[i][j]
                if val == 1:
                    identity = shift_identity(Zc)
                    for row in range(Zc):
                        for column in range(Zc):
                            new_col = (column + 1) % Zc
                            expanded_matrix[i * Zc + row][j * Zc + new_col] = identity[row][column]
                else:
                    for row in range(Zc):
                        for column in range(Zc):
                            expanded_matrix[i * Zc + row][j * Zc + column] = 0

        # A, E, B, C
        for i in range(rows):
            for j in range(cols):
                if j >= 26:
                    continue
                shift = shiftvals[i][j]
                if shift == -1:
                    for row in range(Zc):
                        for column in range(Zc):
                            expanded_matrix[i * Zc + row][j * Zc + column] = 0
                elif shift == 0:
                    identity = shift_identity(Zc)
                    for row in range(Zc):
                        for column in range(Zc):
                            expanded_matrix[i * Zc + row][j * Zc + column] = identity[row][column]
                else:
                    shifted_matrix = shift_identity(Zc)
                    for row in range(Zc):
                        for column in range(Zc):
                            new_col = (column + shift) % Zc
                            expanded_matrix[i * Zc + row][j * Zc + new_col] = shifted_matrix[row][column]
        return expanded_matrix
    else:
        shiftvals = bg2_shiftvals
        rows, cols = bg2_size
        expanded_matrix = [[-1 for _ in range(cols * Zc)] for _ in range(rows * Zc)]
        for i in range(rows):
            for j in range(cols):
                shift = shiftvals[i][j]
                if shift == -1:
                    for row in range(Zc):
                        for column in range(Zc):
                            expanded_matrix[i * Zc + row][j * Zc + column] = 0
                elif shift == 0:
                    identity = shift_identity(Zc)
                    for row in range(Zc):
                        for column in range(Zc):
                            expanded_matrix[i * Zc + row][j * Zc + column] = identity[row][column]
                else:
                    shifted_matrix = shift_identity(Zc)
                    for row in range(Zc):
                        for column in range(Zc):
                            new_col = (column + shift) % Zc
                            expanded_matrix[i * Zc + row][j * Zc + new_col] = shifted_matrix[row][column]
        return expanded_matrix

def print_matrix(matrix):
    for row in matrix:
        print(' '.join(str(x) for x in row))

def generate_codeword(expanded_matrix, infobits):
    # Systematic LDPC encoding: codeword = [infobits] + [parity_bits]
    # Assume first K columns are info bits, remaining are parity bits
    K = len(infobits)
    N = len(expanded_matrix[0])
    M = len(expanded_matrix)
    parity_bits = [0] * (N - K)

    
    for p in range(N - K):
        parity_val = 0
        for row in range(M):
        
            info_sum = 0
            for k in range(K):
                if expanded_matrix[row][k] == 1:
                    info_sum ^= infobits[k]
           
            if expanded_matrix[row][K + p] == 1:
                parity_val ^= info_sum
        parity_bits[p] = parity_val

    codeword = infobits + parity_bits
    return codeword


def main():
    global infobits_in, coderate, Zc

    infobits_in = [0] * 600
    infobits_in = [1 if i % 2 == 0 else 0 for i in range(600)]  
             
    

    infobits_len = len(infobits_in)
    basegraph = calculate_basegraph(infobits_len)
    if(basegraph == 1):
        coderate = code_rates_bg1[0]
    else:   
        coderate = code_rates_bg2[0]  


    print(f"Selected Base Graph: {basegraph}")
    print(infobits_len)
    # Zc hesaplama
    calculate_Zc(infobits_len)
    print(f"Calculated Zc: {Zc}")
    pad_infobits(infobits_in, Zc)
    print(f"Padded Info Bits Length: {len(infobits_in)}")
    expanded_matrix = expand_basegraph(basegraph, Zc)
    print("Expanded Parity-Check Matrix:")
    #print_matrix(expanded_matrix)
    codeword = generate_codeword(expanded_matrix, infobits_in)
    print(f"Generated Codeword Length: {len(codeword)}")
    print(f"Codeword: {codeword}")


if __name__ == "__main__":
     main()