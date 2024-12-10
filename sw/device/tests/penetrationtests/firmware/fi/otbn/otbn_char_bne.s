/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR_BNE FI Penetration Test
*/
.section .text.start
  /* x1=counter, x2&x3=BNE parameters. */
  li   x1, 0
  li   x2, 0xabba
  li   x3, 0xcafe

  /* Try to hit a BNE instruction such that the branch is not taken.
     Then, the counter at the end is different to 0. */
  bne  x2, x3, label0
  addi x1, x1, 1
label0:
  bne  x2, x3, label1
  addi x1, x1, 1
label1:
  bne  x2, x3, label2
  addi x1, x1, 1
label2:
  bne  x2, x3, label3
  addi x1, x1, 1
label3:
  bne  x2, x3, label4
  addi x1, x1, 1
label4:
  bne  x2, x3, label5
  addi x1, x1, 1
label5:
  bne  x2, x3, label6
  addi x1, x1, 1
label6:
  bne  x2, x3, label7
  addi x1, x1, 1
label7:
  bne  x2, x3, label8
  addi x1, x1, 1
label8:
  bne  x2, x3, label9
  addi x1, x1, 1
label9:
  bne  x2, x3, label10
  addi x1, x1, 1
label10:
  bne  x2, x3, label11
  addi x1, x1, 1
label11:
  bne  x2, x3, label12
  addi x1, x1, 1
label12:
  bne  x2, x3, label13
  addi x1, x1, 1
label13:
  bne  x2, x3, label14
  addi x1, x1, 1
label14:
  bne  x2, x3, label15
  addi x1, x1, 1
label15:
  bne  x2, x3, label16
  addi x1, x1, 1
label16:
  bne  x2, x3, label17
  addi x1, x1, 1
label17:
  bne  x2, x3, label18
  addi x1, x1, 1
label18:
  bne  x2, x3, label19
  addi x1, x1, 1
label19:
  bne  x2, x3, label20
  addi x1, x1, 1
label20:
  bne  x2, x3, label21
  addi x1, x1, 1
label21:
  bne  x2, x3, label22
  addi x1, x1, 1
label22:
  bne  x2, x3, label23
  addi x1, x1, 1
label23:
  bne  x2, x3, label24
  addi x1, x1, 1
label24:
  bne  x2, x3, label25
  addi x1, x1, 1
label25:
  bne  x2, x3, label26
  addi x1, x1, 1
label26:
  bne  x2, x3, label27
  addi x1, x1, 1
label27:
  bne  x2, x3, label28
  addi x1, x1, 1
label28:
  bne  x2, x3, label29
  addi x1, x1, 1
label29:
  bne  x2, x3, label30
  addi x1, x1, 1
label30:
  bne  x2, x3, label31
  addi x1, x1, 1
label31:
  bne  x2, x3, label32
  addi x1, x1, 1
label32:
  bne  x2, x3, label33
  addi x1, x1, 1
label33:
  bne  x2, x3, label34
  addi x1, x1, 1
label34:
  bne  x2, x3, label35
  addi x1, x1, 1
label35:
  bne  x2, x3, label36
  addi x1, x1, 1
label36:
  bne  x2, x3, label37
  addi x1, x1, 1
label37:
  bne  x2, x3, label38
  addi x1, x1, 1
label38:
  bne  x2, x3, label39
  addi x1, x1, 1
label39:
  bne  x2, x3, label40
  addi x1, x1, 1
label40:
  bne  x2, x3, label41
  addi x1, x1, 1
label41:
  bne  x2, x3, label42
  addi x1, x1, 1
label42:
  bne  x2, x3, label43
  addi x1, x1, 1
label43:
  bne  x2, x3, label44
  addi x1, x1, 1
label44:
  bne  x2, x3, label45
  addi x1, x1, 1
label45:
  bne  x2, x3, label46
  addi x1, x1, 1
label46:
  bne  x2, x3, label47
  addi x1, x1, 1
label47:
  bne  x2, x3, label48
  addi x1, x1, 1
label48:
  bne  x2, x3, label49
  addi x1, x1, 1
label49:
  bne  x2, x3, label50
  addi x1, x1, 1
label50:
  bne  x2, x3, label51
  addi x1, x1, 1
label51:
  bne  x2, x3, label52
  addi x1, x1, 1
label52:
  bne  x2, x3, label53
  addi x1, x1, 1
label53:
  bne  x2, x3, label54
  addi x1, x1, 1
label54:
  bne  x2, x3, label55
  addi x1, x1, 1
label55:
  bne  x2, x3, label56
  addi x1, x1, 1
label56:
  bne  x2, x3, label57
  addi x1, x1, 1
label57:
  bne  x2, x3, label58
  addi x1, x1, 1
label58:
  bne  x2, x3, label59
  addi x1, x1, 1
label59:
  bne  x2, x3, label60
  addi x1, x1, 1
label60:
  bne  x2, x3, label61
  addi x1, x1, 1
label61:
  bne  x2, x3, label62
  addi x1, x1, 1
label62:
  bne  x2, x3, label63
  addi x1, x1, 1
label63:
  bne  x2, x3, label64
  addi x1, x1, 1
label64:
  bne  x2, x3, label65
  addi x1, x1, 1
label65:
  bne  x2, x3, label66
  addi x1, x1, 1
label66:
  bne  x2, x3, label67
  addi x1, x1, 1
label67:
  bne  x2, x3, label68
  addi x1, x1, 1
label68:
  bne  x2, x3, label69
  addi x1, x1, 1
label69:
  bne  x2, x3, label70
  addi x1, x1, 1
label70:
  bne  x2, x3, label71
  addi x1, x1, 1
label71:
  bne  x2, x3, label72
  addi x1, x1, 1
label72:
  bne  x2, x3, label73
  addi x1, x1, 1
label73:
  bne  x2, x3, label74
  addi x1, x1, 1
label74:
  bne  x2, x3, label75
  addi x1, x1, 1
label75:
  bne  x2, x3, label76
  addi x1, x1, 1
label76:
  bne  x2, x3, label77
  addi x1, x1, 1
label77:
  bne  x2, x3, label78
  addi x1, x1, 1
label78:
  bne  x2, x3, label79
  addi x1, x1, 1
label79:
  bne  x2, x3, label80
  addi x1, x1, 1
label80:
  bne  x2, x3, label81
  addi x1, x1, 1
label81:
  bne  x2, x3, label82
  addi x1, x1, 1
label82:
  bne  x2, x3, label83
  addi x1, x1, 1
label83:
  bne  x2, x3, label84
  addi x1, x1, 1
label84:
  bne  x2, x3, label85
  addi x1, x1, 1
label85:
  bne  x2, x3, label86
  addi x1, x1, 1
label86:
  bne  x2, x3, label87
  addi x1, x1, 1
label87:
  bne  x2, x3, label88
  addi x1, x1, 1
label88:
  bne  x2, x3, label89
  addi x1, x1, 1
label89:
  bne  x2, x3, label90
  addi x1, x1, 1
label90:
  bne  x2, x3, label91
  addi x1, x1, 1
label91:
  bne  x2, x3, label92
  addi x1, x1, 1
label92:
  bne  x2, x3, label93
  addi x1, x1, 1
label93:
  bne  x2, x3, label94
  addi x1, x1, 1
label94:
  bne  x2, x3, label95
  addi x1, x1, 1
label95:
  bne  x2, x3, label96
  addi x1, x1, 1
label96:
  bne  x2, x3, label97
  addi x1, x1, 1
label97:
  bne  x2, x3, label98
  addi x1, x1, 1
label98:
  bne  x2, x3, label99
  addi x1, x1, 1
label99:
  bne  x2, x3, label100
  addi x1, x1, 1
label100:
  bne  x2, x3, label101
  addi x1, x1, 1
label101:
  bne  x2, x3, label102
  addi x1, x1, 1
label102:
  bne  x2, x3, label103
  addi x1, x1, 1
label103:
  bne  x2, x3, label104
  addi x1, x1, 1
label104:
  bne  x2, x3, label105
  addi x1, x1, 1
label105:
  bne  x2, x3, label106
  addi x1, x1, 1
label106:
  bne  x2, x3, label107
  addi x1, x1, 1
label107:
  bne  x2, x3, label108
  addi x1, x1, 1
label108:
  bne  x2, x3, label109
  addi x1, x1, 1
label109:
  bne  x2, x3, label110
  addi x1, x1, 1
label110:
  bne  x2, x3, label111
  addi x1, x1, 1
label111:
  bne  x2, x3, label112
  addi x1, x1, 1
label112:
  bne  x2, x3, label113
  addi x1, x1, 1
label113:
  bne  x2, x3, label114
  addi x1, x1, 1
label114:
  bne  x2, x3, label115
  addi x1, x1, 1
label115:
  bne  x2, x3, label116
  addi x1, x1, 1
label116:
  bne  x2, x3, label117
  addi x1, x1, 1
label117:
  bne  x2, x3, label118
  addi x1, x1, 1
label118:
  bne  x2, x3, label119
  addi x1, x1, 1
label119:
  bne  x2, x3, label120
  addi x1, x1, 1
label120:
  bne  x2, x3, label121
  addi x1, x1, 1
label121:
  bne  x2, x3, label122
  addi x1, x1, 1
label122:
  bne  x2, x3, label123
  addi x1, x1, 1
label123:
  bne  x2, x3, label124
  addi x1, x1, 1
label124:
  bne  x2, x3, label125
  addi x1, x1, 1
label125:
  bne  x2, x3, label126
  addi x1, x1, 1
label126:
  bne  x2, x3, label127
  addi x1, x1, 1
label127:
  bne  x2, x3, label128
  addi x1, x1, 1
label128:
  bne  x2, x3, label129
  addi x1, x1, 1
label129:
  bne  x2, x3, label130
  addi x1, x1, 1
label130:
  bne  x2, x3, label131
  addi x1, x1, 1
label131:
  bne  x2, x3, label132
  addi x1, x1, 1
label132:
  bne  x2, x3, label133
  addi x1, x1, 1
label133:
  bne  x2, x3, label134
  addi x1, x1, 1
label134:
  bne  x2, x3, label135
  addi x1, x1, 1
label135:
  bne  x2, x3, label136
  addi x1, x1, 1
label136:
  bne  x2, x3, label137
  addi x1, x1, 1
label137:
  bne  x2, x3, label138
  addi x1, x1, 1
label138:
  bne  x2, x3, label139
  addi x1, x1, 1
label139:
  bne  x2, x3, label140
  addi x1, x1, 1
label140:
  bne  x2, x3, label141
  addi x1, x1, 1
label141:
  bne  x2, x3, label142
  addi x1, x1, 1
label142:
  bne  x2, x3, label143
  addi x1, x1, 1
label143:
  bne  x2, x3, label144
  addi x1, x1, 1
label144:
  bne  x2, x3, label145
  addi x1, x1, 1
label145:
  bne  x2, x3, label146
  addi x1, x1, 1
label146:
  bne  x2, x3, label147
  addi x1, x1, 1
label147:
  bne  x2, x3, label148
  addi x1, x1, 1
label148:
  bne  x2, x3, label149
  addi x1, x1, 1
label149:
  bne  x2, x3, label150
  addi x1, x1, 1
label150:
  bne  x2, x3, label151
  addi x1, x1, 1
label151:
  bne  x2, x3, label152
  addi x1, x1, 1
label152:
  bne  x2, x3, label153
  addi x1, x1, 1
label153:
  bne  x2, x3, label154
  addi x1, x1, 1
label154:
  bne  x2, x3, label155
  addi x1, x1, 1
label155:
  bne  x2, x3, label156
  addi x1, x1, 1
label156:
  bne  x2, x3, label157
  addi x1, x1, 1
label157:
  bne  x2, x3, label158
  addi x1, x1, 1
label158:
  bne  x2, x3, label159
  addi x1, x1, 1
label159:
  bne  x2, x3, label160
  addi x1, x1, 1
label160:
  bne  x2, x3, label161
  addi x1, x1, 1
label161:
  bne  x2, x3, label162
  addi x1, x1, 1
label162:
  bne  x2, x3, label163
  addi x1, x1, 1
label163:
  bne  x2, x3, label164
  addi x1, x1, 1
label164:
  bne  x2, x3, label165
  addi x1, x1, 1
label165:
  bne  x2, x3, label166
  addi x1, x1, 1
label166:
  bne  x2, x3, label167
  addi x1, x1, 1
label167:
  bne  x2, x3, label168
  addi x1, x1, 1
label168:
  bne  x2, x3, label169
  addi x1, x1, 1
label169:
  bne  x2, x3, label170
  addi x1, x1, 1
label170:
  bne  x2, x3, label171
  addi x1, x1, 1
label171:
  bne  x2, x3, label172
  addi x1, x1, 1
label172:
  bne  x2, x3, label173
  addi x1, x1, 1
label173:
  bne  x2, x3, label174
  addi x1, x1, 1
label174:
  bne  x2, x3, label175
  addi x1, x1, 1
label175:
  bne  x2, x3, label176
  addi x1, x1, 1
label176:
  bne  x2, x3, label177
  addi x1, x1, 1
label177:
  bne  x2, x3, label178
  addi x1, x1, 1
label178:
  bne  x2, x3, label179
  addi x1, x1, 1
label179:
  bne  x2, x3, label180
  addi x1, x1, 1
label180:
  bne  x2, x3, label181
  addi x1, x1, 1
label181:
  bne  x2, x3, label182
  addi x1, x1, 1
label182:
  bne  x2, x3, label183
  addi x1, x1, 1
label183:
  bne  x2, x3, label184
  addi x1, x1, 1
label184:
  bne  x2, x3, label185
  addi x1, x1, 1
label185:
  bne  x2, x3, label186
  addi x1, x1, 1
label186:
  bne  x2, x3, label187
  addi x1, x1, 1
label187:
  bne  x2, x3, label188
  addi x1, x1, 1
label188:
  bne  x2, x3, label189
  addi x1, x1, 1
label189:
  bne  x2, x3, label190
  addi x1, x1, 1
label190:
  bne  x2, x3, label191
  addi x1, x1, 1
label191:
  bne  x2, x3, label192
  addi x1, x1, 1
label192:
  bne  x2, x3, label193
  addi x1, x1, 1
label193:
  bne  x2, x3, label194
  addi x1, x1, 1
label194:
  bne  x2, x3, label195
  addi x1, x1, 1
label195:
  bne  x2, x3, label196
  addi x1, x1, 1
label196:
  bne  x2, x3, label197
  addi x1, x1, 1
label197:
  bne  x2, x3, label198
  addi x1, x1, 1
label198:
  bne  x2, x3, label199
  addi x1, x1, 1
label199:
  bne  x2, x3, label200
  addi x1, x1, 1
label200:
  bne  x2, x3, label201
  addi x1, x1, 1
label201:
  bne  x2, x3, label202
  addi x1, x1, 1
label202:
  bne  x2, x3, label203
  addi x1, x1, 1
label203:
  bne  x2, x3, label204
  addi x1, x1, 1
label204:
  bne  x2, x3, label205
  addi x1, x1, 1
label205:
  bne  x2, x3, label206
  addi x1, x1, 1
label206:
  bne  x2, x3, label207
  addi x1, x1, 1
label207:
  bne  x2, x3, label208
  addi x1, x1, 1
label208:
  bne  x2, x3, label209
  addi x1, x1, 1
label209:
  bne  x2, x3, label210
  addi x1, x1, 1
label210:
  bne  x2, x3, label211
  addi x1, x1, 1
label211:
  bne  x2, x3, label212
  addi x1, x1, 1
label212:
  bne  x2, x3, label213
  addi x1, x1, 1
label213:
  bne  x2, x3, label214
  addi x1, x1, 1
label214:
  bne  x2, x3, label215
  addi x1, x1, 1
label215:
  bne  x2, x3, label216
  addi x1, x1, 1
label216:
  bne  x2, x3, label217
  addi x1, x1, 1
label217:
  bne  x2, x3, label218
  addi x1, x1, 1
label218:
  bne  x2, x3, label219
  addi x1, x1, 1
label219:
  bne  x2, x3, label220
  addi x1, x1, 1
label220:
  bne  x2, x3, label221
  addi x1, x1, 1
label221:
  bne  x2, x3, label222
  addi x1, x1, 1
label222:
  bne  x2, x3, label223
  addi x1, x1, 1
label223:
  bne  x2, x3, label224
  addi x1, x1, 1
label224:
  bne  x2, x3, label225
  addi x1, x1, 1
label225:
  bne  x2, x3, label226
  addi x1, x1, 1
label226:
  bne  x2, x3, label227
  addi x1, x1, 1
label227:
  bne  x2, x3, label228
  addi x1, x1, 1
label228:
  bne  x2, x3, label229
  addi x1, x1, 1
label229:
  bne  x2, x3, label230
  addi x1, x1, 1
label230:
  bne  x2, x3, label231
  addi x1, x1, 1
label231:
  bne  x2, x3, label232
  addi x1, x1, 1
label232:
  bne  x2, x3, label233
  addi x1, x1, 1
label233:
  bne  x2, x3, label234
  addi x1, x1, 1
label234:
  bne  x2, x3, label235
  addi x1, x1, 1
label235:
  bne  x2, x3, label236
  addi x1, x1, 1
label236:
  bne  x2, x3, label237
  addi x1, x1, 1
label237:
  bne  x2, x3, label238
  addi x1, x1, 1
label238:
  bne  x2, x3, label239
  addi x1, x1, 1
label239:
  bne  x2, x3, label240
  addi x1, x1, 1
label240:
  bne  x2, x3, label241
  addi x1, x1, 1
label241:
  bne  x2, x3, label242
  addi x1, x1, 1
label242:
  bne  x2, x3, label243
  addi x1, x1, 1
label243:
  bne  x2, x3, label244
  addi x1, x1, 1
label244:
  bne  x2, x3, label245
  addi x1, x1, 1
label245:
  bne  x2, x3, label246
  addi x1, x1, 1
label246:
  bne  x2, x3, label247
  addi x1, x1, 1
label247:
  bne  x2, x3, label248
  addi x1, x1, 1
label248:
  bne  x2, x3, label249
  addi x1, x1, 1
label249:
  bne  x2, x3, label250
  addi x1, x1, 1
label250:
  bne  x2, x3, label251
  addi x1, x1, 1
label251:
  bne  x2, x3, label252
  addi x1, x1, 1
label252:
  bne  x2, x3, label253
  addi x1, x1, 1
label253:
  bne  x2, x3, label254
  addi x1, x1, 1
label254:
  bne  x2, x3, label255
  addi x1, x1, 1
label255:
  bne  x2, x3, label256
  addi x1, x1, 1
label256:
  bne  x2, x3, label257
  addi x1, x1, 1
label257:
  bne  x2, x3, label258
  addi x1, x1, 1
label258:
  bne  x2, x3, label259
  addi x1, x1, 1
label259:
  bne  x2, x3, label260
  addi x1, x1, 1
label260:
  bne  x2, x3, label261
  addi x1, x1, 1
label261:
  bne  x2, x3, label262
  addi x1, x1, 1
label262:
  bne  x2, x3, label263
  addi x1, x1, 1
label263:
  bne  x2, x3, label264
  addi x1, x1, 1
label264:
  bne  x2, x3, label265
  addi x1, x1, 1
label265:
  bne  x2, x3, label266
  addi x1, x1, 1
label266:
  bne  x2, x3, label267
  addi x1, x1, 1
label267:
  bne  x2, x3, label268
  addi x1, x1, 1
label268:
  bne  x2, x3, label269
  addi x1, x1, 1
label269:
  bne  x2, x3, label270
  addi x1, x1, 1
label270:
  bne  x2, x3, label271
  addi x1, x1, 1
label271:
  bne  x2, x3, label272
  addi x1, x1, 1
label272:
  bne  x2, x3, label273
  addi x1, x1, 1
label273:
  bne  x2, x3, label274
  addi x1, x1, 1
label274:
  bne  x2, x3, label275
  addi x1, x1, 1
label275:
  bne  x2, x3, label276
  addi x1, x1, 1
label276:
  bne  x2, x3, label277
  addi x1, x1, 1
label277:
  bne  x2, x3, label278
  addi x1, x1, 1
label278:
  bne  x2, x3, label279
  addi x1, x1, 1
label279:
  bne  x2, x3, label280
  addi x1, x1, 1
label280:
  bne  x2, x3, label281
  addi x1, x1, 1
label281:
  bne  x2, x3, label282
  addi x1, x1, 1
label282:
  bne  x2, x3, label283
  addi x1, x1, 1
label283:
  bne  x2, x3, label284
  addi x1, x1, 1
label284:
  bne  x2, x3, label285
  addi x1, x1, 1
label285:
  bne  x2, x3, label286
  addi x1, x1, 1
label286:
  bne  x2, x3, label287
  addi x1, x1, 1
label287:
  bne  x2, x3, label288
  addi x1, x1, 1
label288:
  bne  x2, x3, label289
  addi x1, x1, 1
label289:
  bne  x2, x3, label290
  addi x1, x1, 1
label290:
  bne  x2, x3, label291
  addi x1, x1, 1
label291:
  bne  x2, x3, label292
  addi x1, x1, 1
label292:
  bne  x2, x3, label293
  addi x1, x1, 1
label293:
  bne  x2, x3, label294
  addi x1, x1, 1
label294:
  bne  x2, x3, label295
  addi x1, x1, 1
label295:
  bne  x2, x3, label296
  addi x1, x1, 1
label296:
  bne  x2, x3, label297
  addi x1, x1, 1
label297:
  bne  x2, x3, label298
  addi x1, x1, 1
label298:
  bne  x2, x3, label299
  addi x1, x1, 1
label299:
  bne  x2, x3, label300
  addi x1, x1, 1
label300:
  bne  x2, x3, label301
  addi x1, x1, 1
label301:
  bne  x2, x3, label302
  addi x1, x1, 1
label302:
  bne  x2, x3, label303
  addi x1, x1, 1
label303:
  bne  x2, x3, label304
  addi x1, x1, 1
label304:
  bne  x2, x3, label305
  addi x1, x1, 1
label305:
  bne  x2, x3, label306
  addi x1, x1, 1
label306:
  bne  x2, x3, label307
  addi x1, x1, 1
label307:
  bne  x2, x3, label308
  addi x1, x1, 1
label308:
  bne  x2, x3, label309
  addi x1, x1, 1
label309:
  bne  x2, x3, label310
  addi x1, x1, 1
label310:
  bne  x2, x3, label311
  addi x1, x1, 1
label311:
  bne  x2, x3, label312
  addi x1, x1, 1
label312:
  bne  x2, x3, label313
  addi x1, x1, 1
label313:
  bne  x2, x3, label314
  addi x1, x1, 1
label314:
  bne  x2, x3, label315
  addi x1, x1, 1
label315:
  bne  x2, x3, label316
  addi x1, x1, 1
label316:
  bne  x2, x3, label317
  addi x1, x1, 1
label317:
  bne  x2, x3, label318
  addi x1, x1, 1
label318:
  bne  x2, x3, label319
  addi x1, x1, 1
label319:
  bne  x2, x3, label320
  addi x1, x1, 1
label320:
  bne  x2, x3, label321
  addi x1, x1, 1
label321:
  bne  x2, x3, label322
  addi x1, x1, 1
label322:
  bne  x2, x3, label323
  addi x1, x1, 1
label323:
  bne  x2, x3, label324
  addi x1, x1, 1
label324:
  bne  x2, x3, label325
  addi x1, x1, 1
label325:
  bne  x2, x3, label326
  addi x1, x1, 1
label326:
  bne  x2, x3, label327
  addi x1, x1, 1
label327:
  bne  x2, x3, label328
  addi x1, x1, 1
label328:
  bne  x2, x3, label329
  addi x1, x1, 1
label329:
  bne  x2, x3, label330
  addi x1, x1, 1
label330:
  bne  x2, x3, label331
  addi x1, x1, 1
label331:
  bne  x2, x3, label332
  addi x1, x1, 1
label332:
  bne  x2, x3, label333
  addi x1, x1, 1
label333:
  bne  x2, x3, label334
  addi x1, x1, 1
label334:
  bne  x2, x3, label335
  addi x1, x1, 1
label335:
  bne  x2, x3, label336
  addi x1, x1, 1
label336:
  bne  x2, x3, label337
  addi x1, x1, 1
label337:
  bne  x2, x3, label338
  addi x1, x1, 1
label338:
  bne  x2, x3, label339
  addi x1, x1, 1
label339:
  bne  x2, x3, label340
  addi x1, x1, 1
label340:
  bne  x2, x3, label341
  addi x1, x1, 1
label341:
  bne  x2, x3, label342
  addi x1, x1, 1
label342:
  bne  x2, x3, label343
  addi x1, x1, 1
label343:
  bne  x2, x3, label344
  addi x1, x1, 1
label344:
  bne  x2, x3, label345
  addi x1, x1, 1
label345:
  bne  x2, x3, label346
  addi x1, x1, 1
label346:
  bne  x2, x3, label347
  addi x1, x1, 1
label347:
  bne  x2, x3, label348
  addi x1, x1, 1
label348:
  bne  x2, x3, label349
  addi x1, x1, 1
label349:
  bne  x2, x3, label350
  addi x1, x1, 1
label350:
  bne  x2, x3, label351
  addi x1, x1, 1
label351:
  bne  x2, x3, label352
  addi x1, x1, 1
label352:
  bne  x2, x3, label353
  addi x1, x1, 1
label353:
  bne  x2, x3, label354
  addi x1, x1, 1
label354:
  bne  x2, x3, label355
  addi x1, x1, 1
label355:
  bne  x2, x3, label356
  addi x1, x1, 1
label356:
  bne  x2, x3, label357
  addi x1, x1, 1
label357:
  bne  x2, x3, label358
  addi x1, x1, 1
label358:
  bne  x2, x3, label359
  addi x1, x1, 1
label359:
  bne  x2, x3, label360
  addi x1, x1, 1
label360:
  bne  x2, x3, label361
  addi x1, x1, 1
label361:
  bne  x2, x3, label362
  addi x1, x1, 1
label362:
  bne  x2, x3, label363
  addi x1, x1, 1
label363:
  bne  x2, x3, label364
  addi x1, x1, 1
label364:
  bne  x2, x3, label365
  addi x1, x1, 1
label365:
  bne  x2, x3, label366
  addi x1, x1, 1
label366:
  bne  x2, x3, label367
  addi x1, x1, 1
label367:
  bne  x2, x3, label368
  addi x1, x1, 1
label368:
  bne  x2, x3, label369
  addi x1, x1, 1
label369:
  bne  x2, x3, label370
  addi x1, x1, 1
label370:
  bne  x2, x3, label371
  addi x1, x1, 1
label371:
  bne  x2, x3, label372
  addi x1, x1, 1
label372:
  bne  x2, x3, label373
  addi x1, x1, 1
label373:
  bne  x2, x3, label374
  addi x1, x1, 1
label374:
  bne  x2, x3, label375
  addi x1, x1, 1
label375:
  bne  x2, x3, label376
  addi x1, x1, 1
label376:
  bne  x2, x3, label377
  addi x1, x1, 1
label377:
  bne  x2, x3, label378
  addi x1, x1, 1
label378:
  bne  x2, x3, label379
  addi x1, x1, 1
label379:
  bne  x2, x3, label380
  addi x1, x1, 1
label380:
  bne  x2, x3, label381
  addi x1, x1, 1
label381:
  bne  x2, x3, label382
  addi x1, x1, 1
label382:
  bne  x2, x3, label383
  addi x1, x1, 1
label383:
  bne  x2, x3, label384
  addi x1, x1, 1
label384:
  bne  x2, x3, label385
  addi x1, x1, 1
label385:
  bne  x2, x3, label386
  addi x1, x1, 1
label386:
  bne  x2, x3, label387
  addi x1, x1, 1
label387:
  bne  x2, x3, label388
  addi x1, x1, 1
label388:
  bne  x2, x3, label389
  addi x1, x1, 1
label389:
  bne  x2, x3, label390
  addi x1, x1, 1
label390:
  bne  x2, x3, label391
  addi x1, x1, 1
label391:
  bne  x2, x3, label392
  addi x1, x1, 1
label392:
  bne  x2, x3, label393
  addi x1, x1, 1
label393:
  bne  x2, x3, label394
  addi x1, x1, 1
label394:
  bne  x2, x3, label395
  addi x1, x1, 1
label395:
  bne  x2, x3, label396
  addi x1, x1, 1
label396:
  bne  x2, x3, label397
  addi x1, x1, 1
label397:
  bne  x2, x3, label398
  addi x1, x1, 1
label398:
  bne  x2, x3, label399
  addi x1, x1, 1
label399:
  bne  x2, x3, label400
  addi x1, x1, 1
label400:
  bne  x2, x3, label401
  addi x1, x1, 1
label401:
  bne  x2, x3, label402
  addi x1, x1, 1
label402:
  bne  x2, x3, label403
  addi x1, x1, 1
label403:
  bne  x2, x3, label404
  addi x1, x1, 1
label404:
  bne  x2, x3, label405
  addi x1, x1, 1
label405:
  bne  x2, x3, label406
  addi x1, x1, 1
label406:
  bne  x2, x3, label407
  addi x1, x1, 1
label407:
  bne  x2, x3, label408
  addi x1, x1, 1
label408:
  bne  x2, x3, label409
  addi x1, x1, 1
label409:
  bne  x2, x3, label410
  addi x1, x1, 1
label410:
  bne  x2, x3, label411
  addi x1, x1, 1
label411:
  bne  x2, x3, label412
  addi x1, x1, 1
label412:
  bne  x2, x3, label413
  addi x1, x1, 1
label413:
  bne  x2, x3, label414
  addi x1, x1, 1
label414:
  bne  x2, x3, label415
  addi x1, x1, 1
label415:
  bne  x2, x3, label416
  addi x1, x1, 1
label416:
  bne  x2, x3, label417
  addi x1, x1, 1
label417:
  bne  x2, x3, label418
  addi x1, x1, 1
label418:
  bne  x2, x3, label419
  addi x1, x1, 1
label419:
  bne  x2, x3, label420
  addi x1, x1, 1
label420:
  bne  x2, x3, label421
  addi x1, x1, 1
label421:
  bne  x2, x3, label422
  addi x1, x1, 1
label422:
  bne  x2, x3, label423
  addi x1, x1, 1
label423:
  bne  x2, x3, label424
  addi x1, x1, 1
label424:
  bne  x2, x3, label425
  addi x1, x1, 1
label425:
  bne  x2, x3, label426
  addi x1, x1, 1
label426:
  bne  x2, x3, label427
  addi x1, x1, 1
label427:
  bne  x2, x3, label428
  addi x1, x1, 1
label428:
  bne  x2, x3, label429
  addi x1, x1, 1
label429:
  bne  x2, x3, label430
  addi x1, x1, 1
label430:
  bne  x2, x3, label431
  addi x1, x1, 1
label431:
  bne  x2, x3, label432
  addi x1, x1, 1
label432:
  bne  x2, x3, label433
  addi x1, x1, 1
label433:
  bne  x2, x3, label434
  addi x1, x1, 1
label434:
  bne  x2, x3, label435
  addi x1, x1, 1
label435:
  bne  x2, x3, label436
  addi x1, x1, 1
label436:
  bne  x2, x3, label437
  addi x1, x1, 1
label437:
  bne  x2, x3, label438
  addi x1, x1, 1
label438:
  bne  x2, x3, label439
  addi x1, x1, 1
label439:
  bne  x2, x3, label440
  addi x1, x1, 1
label440:
  bne  x2, x3, label441
  addi x1, x1, 1
label441:
  bne  x2, x3, label442
  addi x1, x1, 1
label442:
  bne  x2, x3, label443
  addi x1, x1, 1
label443:
  bne  x2, x3, label444
  addi x1, x1, 1
label444:
  bne  x2, x3, label445
  addi x1, x1, 1
label445:
  bne  x2, x3, label446
  addi x1, x1, 1
label446:
  bne  x2, x3, label447
  addi x1, x1, 1
label447:
  bne  x2, x3, label448
  addi x1, x1, 1
label448:
  bne  x2, x3, label449
  addi x1, x1, 1
label449:
  bne  x2, x3, label450
  addi x1, x1, 1
label450:
  bne  x2, x3, label451
  addi x1, x1, 1
label451:
  bne  x2, x3, label452
  addi x1, x1, 1
label452:
  bne  x2, x3, label453
  addi x1, x1, 1
label453:
  bne  x2, x3, label454
  addi x1, x1, 1
label454:
  bne  x2, x3, label455
  addi x1, x1, 1
label455:
  bne  x2, x3, label456
  addi x1, x1, 1
label456:
  bne  x2, x3, label457
  addi x1, x1, 1
label457:
  bne  x2, x3, label458
  addi x1, x1, 1
label458:
  bne  x2, x3, label459
  addi x1, x1, 1
label459:
  bne  x2, x3, label460
  addi x1, x1, 1
label460:
  bne  x2, x3, label461
  addi x1, x1, 1
label461:
  bne  x2, x3, label462
  addi x1, x1, 1
label462:
  bne  x2, x3, label463
  addi x1, x1, 1
label463:
  bne  x2, x3, label464
  addi x1, x1, 1
label464:
  bne  x2, x3, label465
  addi x1, x1, 1
label465:
  bne  x2, x3, label466
  addi x1, x1, 1
label466:
  bne  x2, x3, label467
  addi x1, x1, 1
label467:
  bne  x2, x3, label468
  addi x1, x1, 1
label468:
  bne  x2, x3, label469
  addi x1, x1, 1
label469:
  bne  x2, x3, label470
  addi x1, x1, 1
label470:
  bne  x2, x3, label471
  addi x1, x1, 1
label471:
  bne  x2, x3, label472
  addi x1, x1, 1
label472:
  bne  x2, x3, label473
  addi x1, x1, 1
label473:
  bne  x2, x3, label474
  addi x1, x1, 1
label474:
  bne  x2, x3, label475
  addi x1, x1, 1
label475:
  bne  x2, x3, label476
  addi x1, x1, 1
label476:
  bne  x2, x3, label477
  addi x1, x1, 1
label477:
  bne  x2, x3, label478
  addi x1, x1, 1
label478:
  bne  x2, x3, label479
  addi x1, x1, 1
label479:
  bne  x2, x3, label480
  addi x1, x1, 1
label480:
  bne  x2, x3, label481
  addi x1, x1, 1
label481:
  bne  x2, x3, label482
  addi x1, x1, 1
label482:
  bne  x2, x3, label483
  addi x1, x1, 1
label483:
  bne  x2, x3, label484
  addi x1, x1, 1
label484:
  bne  x2, x3, label485
  addi x1, x1, 1
label485:
  bne  x2, x3, label486
  addi x1, x1, 1
label486:
  bne  x2, x3, label487
  addi x1, x1, 1
label487:
  bne  x2, x3, label488
  addi x1, x1, 1
label488:
  bne  x2, x3, label489
  addi x1, x1, 1
label489:
  bne  x2, x3, label490
  addi x1, x1, 1
label490:
  bne  x2, x3, label491
  addi x1, x1, 1
label491:
  bne  x2, x3, label492
  addi x1, x1, 1
label492:
  bne  x2, x3, label493
  addi x1, x1, 1
label493:
  bne  x2, x3, label494
  addi x1, x1, 1
label494:
  bne  x2, x3, label495
  addi x1, x1, 1
label495:
  bne  x2, x3, label496
  addi x1, x1, 1
label496:
  bne  x2, x3, label497
  addi x1, x1, 1
label497:
  bne  x2, x3, label498
  addi x1, x1, 1
label498:
  bne  x2, x3, label499
  addi x1, x1, 1
label499:


  /* Write counter into DEM. */
  la   x5, res
  sw   x1, 0(x5)

  ecall

.data
  .balign 32
  .globl res
  res:
    .zero 4
