/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR_BEQ FI Penetration Test
*/
.section .text.start
  /* x1=counter, x2&x3=BEQ parameters. */
  li   x1, 0
  li   x2, 0xabba
  li   x3, 0xabba

  /* Try to hit a BEQ instruction such that the branch is not taken.
     Then, the counter at the end is different to 0. */
  beq  x2, x3, label0
  addi x1, x1, 1
label0:
  beq  x2, x3, label1
  addi x1, x1, 1
label1:
  beq  x2, x3, label2
  addi x1, x1, 1
label2:
  beq  x2, x3, label3
  addi x1, x1, 1
label3:
  beq  x2, x3, label4
  addi x1, x1, 1
label4:
  beq  x2, x3, label5
  addi x1, x1, 1
label5:
  beq  x2, x3, label6
  addi x1, x1, 1
label6:
  beq  x2, x3, label7
  addi x1, x1, 1
label7:
  beq  x2, x3, label8
  addi x1, x1, 1
label8:
  beq  x2, x3, label9
  addi x1, x1, 1
label9:
  beq  x2, x3, label10
  addi x1, x1, 1
label10:
  beq  x2, x3, label11
  addi x1, x1, 1
label11:
  beq  x2, x3, label12
  addi x1, x1, 1
label12:
  beq  x2, x3, label13
  addi x1, x1, 1
label13:
  beq  x2, x3, label14
  addi x1, x1, 1
label14:
  beq  x2, x3, label15
  addi x1, x1, 1
label15:
  beq  x2, x3, label16
  addi x1, x1, 1
label16:
  beq  x2, x3, label17
  addi x1, x1, 1
label17:
  beq  x2, x3, label18
  addi x1, x1, 1
label18:
  beq  x2, x3, label19
  addi x1, x1, 1
label19:
  beq  x2, x3, label20
  addi x1, x1, 1
label20:
  beq  x2, x3, label21
  addi x1, x1, 1
label21:
  beq  x2, x3, label22
  addi x1, x1, 1
label22:
  beq  x2, x3, label23
  addi x1, x1, 1
label23:
  beq  x2, x3, label24
  addi x1, x1, 1
label24:
  beq  x2, x3, label25
  addi x1, x1, 1
label25:
  beq  x2, x3, label26
  addi x1, x1, 1
label26:
  beq  x2, x3, label27
  addi x1, x1, 1
label27:
  beq  x2, x3, label28
  addi x1, x1, 1
label28:
  beq  x2, x3, label29
  addi x1, x1, 1
label29:
  beq  x2, x3, label30
  addi x1, x1, 1
label30:
  beq  x2, x3, label31
  addi x1, x1, 1
label31:
  beq  x2, x3, label32
  addi x1, x1, 1
label32:
  beq  x2, x3, label33
  addi x1, x1, 1
label33:
  beq  x2, x3, label34
  addi x1, x1, 1
label34:
  beq  x2, x3, label35
  addi x1, x1, 1
label35:
  beq  x2, x3, label36
  addi x1, x1, 1
label36:
  beq  x2, x3, label37
  addi x1, x1, 1
label37:
  beq  x2, x3, label38
  addi x1, x1, 1
label38:
  beq  x2, x3, label39
  addi x1, x1, 1
label39:
  beq  x2, x3, label40
  addi x1, x1, 1
label40:
  beq  x2, x3, label41
  addi x1, x1, 1
label41:
  beq  x2, x3, label42
  addi x1, x1, 1
label42:
  beq  x2, x3, label43
  addi x1, x1, 1
label43:
  beq  x2, x3, label44
  addi x1, x1, 1
label44:
  beq  x2, x3, label45
  addi x1, x1, 1
label45:
  beq  x2, x3, label46
  addi x1, x1, 1
label46:
  beq  x2, x3, label47
  addi x1, x1, 1
label47:
  beq  x2, x3, label48
  addi x1, x1, 1
label48:
  beq  x2, x3, label49
  addi x1, x1, 1
label49:
  beq  x2, x3, label50
  addi x1, x1, 1
label50:
  beq  x2, x3, label51
  addi x1, x1, 1
label51:
  beq  x2, x3, label52
  addi x1, x1, 1
label52:
  beq  x2, x3, label53
  addi x1, x1, 1
label53:
  beq  x2, x3, label54
  addi x1, x1, 1
label54:
  beq  x2, x3, label55
  addi x1, x1, 1
label55:
  beq  x2, x3, label56
  addi x1, x1, 1
label56:
  beq  x2, x3, label57
  addi x1, x1, 1
label57:
  beq  x2, x3, label58
  addi x1, x1, 1
label58:
  beq  x2, x3, label59
  addi x1, x1, 1
label59:
  beq  x2, x3, label60
  addi x1, x1, 1
label60:
  beq  x2, x3, label61
  addi x1, x1, 1
label61:
  beq  x2, x3, label62
  addi x1, x1, 1
label62:
  beq  x2, x3, label63
  addi x1, x1, 1
label63:
  beq  x2, x3, label64
  addi x1, x1, 1
label64:
  beq  x2, x3, label65
  addi x1, x1, 1
label65:
  beq  x2, x3, label66
  addi x1, x1, 1
label66:
  beq  x2, x3, label67
  addi x1, x1, 1
label67:
  beq  x2, x3, label68
  addi x1, x1, 1
label68:
  beq  x2, x3, label69
  addi x1, x1, 1
label69:
  beq  x2, x3, label70
  addi x1, x1, 1
label70:
  beq  x2, x3, label71
  addi x1, x1, 1
label71:
  beq  x2, x3, label72
  addi x1, x1, 1
label72:
  beq  x2, x3, label73
  addi x1, x1, 1
label73:
  beq  x2, x3, label74
  addi x1, x1, 1
label74:
  beq  x2, x3, label75
  addi x1, x1, 1
label75:
  beq  x2, x3, label76
  addi x1, x1, 1
label76:
  beq  x2, x3, label77
  addi x1, x1, 1
label77:
  beq  x2, x3, label78
  addi x1, x1, 1
label78:
  beq  x2, x3, label79
  addi x1, x1, 1
label79:
  beq  x2, x3, label80
  addi x1, x1, 1
label80:
  beq  x2, x3, label81
  addi x1, x1, 1
label81:
  beq  x2, x3, label82
  addi x1, x1, 1
label82:
  beq  x2, x3, label83
  addi x1, x1, 1
label83:
  beq  x2, x3, label84
  addi x1, x1, 1
label84:
  beq  x2, x3, label85
  addi x1, x1, 1
label85:
  beq  x2, x3, label86
  addi x1, x1, 1
label86:
  beq  x2, x3, label87
  addi x1, x1, 1
label87:
  beq  x2, x3, label88
  addi x1, x1, 1
label88:
  beq  x2, x3, label89
  addi x1, x1, 1
label89:
  beq  x2, x3, label90
  addi x1, x1, 1
label90:
  beq  x2, x3, label91
  addi x1, x1, 1
label91:
  beq  x2, x3, label92
  addi x1, x1, 1
label92:
  beq  x2, x3, label93
  addi x1, x1, 1
label93:
  beq  x2, x3, label94
  addi x1, x1, 1
label94:
  beq  x2, x3, label95
  addi x1, x1, 1
label95:
  beq  x2, x3, label96
  addi x1, x1, 1
label96:
  beq  x2, x3, label97
  addi x1, x1, 1
label97:
  beq  x2, x3, label98
  addi x1, x1, 1
label98:
  beq  x2, x3, label99
  addi x1, x1, 1
label99:
  beq  x2, x3, label100
  addi x1, x1, 1
label100:
  beq  x2, x3, label101
  addi x1, x1, 1
label101:
  beq  x2, x3, label102
  addi x1, x1, 1
label102:
  beq  x2, x3, label103
  addi x1, x1, 1
label103:
  beq  x2, x3, label104
  addi x1, x1, 1
label104:
  beq  x2, x3, label105
  addi x1, x1, 1
label105:
  beq  x2, x3, label106
  addi x1, x1, 1
label106:
  beq  x2, x3, label107
  addi x1, x1, 1
label107:
  beq  x2, x3, label108
  addi x1, x1, 1
label108:
  beq  x2, x3, label109
  addi x1, x1, 1
label109:
  beq  x2, x3, label110
  addi x1, x1, 1
label110:
  beq  x2, x3, label111
  addi x1, x1, 1
label111:
  beq  x2, x3, label112
  addi x1, x1, 1
label112:
  beq  x2, x3, label113
  addi x1, x1, 1
label113:
  beq  x2, x3, label114
  addi x1, x1, 1
label114:
  beq  x2, x3, label115
  addi x1, x1, 1
label115:
  beq  x2, x3, label116
  addi x1, x1, 1
label116:
  beq  x2, x3, label117
  addi x1, x1, 1
label117:
  beq  x2, x3, label118
  addi x1, x1, 1
label118:
  beq  x2, x3, label119
  addi x1, x1, 1
label119:
  beq  x2, x3, label120
  addi x1, x1, 1
label120:
  beq  x2, x3, label121
  addi x1, x1, 1
label121:
  beq  x2, x3, label122
  addi x1, x1, 1
label122:
  beq  x2, x3, label123
  addi x1, x1, 1
label123:
  beq  x2, x3, label124
  addi x1, x1, 1
label124:
  beq  x2, x3, label125
  addi x1, x1, 1
label125:
  beq  x2, x3, label126
  addi x1, x1, 1
label126:
  beq  x2, x3, label127
  addi x1, x1, 1
label127:
  beq  x2, x3, label128
  addi x1, x1, 1
label128:
  beq  x2, x3, label129
  addi x1, x1, 1
label129:
  beq  x2, x3, label130
  addi x1, x1, 1
label130:
  beq  x2, x3, label131
  addi x1, x1, 1
label131:
  beq  x2, x3, label132
  addi x1, x1, 1
label132:
  beq  x2, x3, label133
  addi x1, x1, 1
label133:
  beq  x2, x3, label134
  addi x1, x1, 1
label134:
  beq  x2, x3, label135
  addi x1, x1, 1
label135:
  beq  x2, x3, label136
  addi x1, x1, 1
label136:
  beq  x2, x3, label137
  addi x1, x1, 1
label137:
  beq  x2, x3, label138
  addi x1, x1, 1
label138:
  beq  x2, x3, label139
  addi x1, x1, 1
label139:
  beq  x2, x3, label140
  addi x1, x1, 1
label140:
  beq  x2, x3, label141
  addi x1, x1, 1
label141:
  beq  x2, x3, label142
  addi x1, x1, 1
label142:
  beq  x2, x3, label143
  addi x1, x1, 1
label143:
  beq  x2, x3, label144
  addi x1, x1, 1
label144:
  beq  x2, x3, label145
  addi x1, x1, 1
label145:
  beq  x2, x3, label146
  addi x1, x1, 1
label146:
  beq  x2, x3, label147
  addi x1, x1, 1
label147:
  beq  x2, x3, label148
  addi x1, x1, 1
label148:
  beq  x2, x3, label149
  addi x1, x1, 1
label149:
  beq  x2, x3, label150
  addi x1, x1, 1
label150:
  beq  x2, x3, label151
  addi x1, x1, 1
label151:
  beq  x2, x3, label152
  addi x1, x1, 1
label152:
  beq  x2, x3, label153
  addi x1, x1, 1
label153:
  beq  x2, x3, label154
  addi x1, x1, 1
label154:
  beq  x2, x3, label155
  addi x1, x1, 1
label155:
  beq  x2, x3, label156
  addi x1, x1, 1
label156:
  beq  x2, x3, label157
  addi x1, x1, 1
label157:
  beq  x2, x3, label158
  addi x1, x1, 1
label158:
  beq  x2, x3, label159
  addi x1, x1, 1
label159:
  beq  x2, x3, label160
  addi x1, x1, 1
label160:
  beq  x2, x3, label161
  addi x1, x1, 1
label161:
  beq  x2, x3, label162
  addi x1, x1, 1
label162:
  beq  x2, x3, label163
  addi x1, x1, 1
label163:
  beq  x2, x3, label164
  addi x1, x1, 1
label164:
  beq  x2, x3, label165
  addi x1, x1, 1
label165:
  beq  x2, x3, label166
  addi x1, x1, 1
label166:
  beq  x2, x3, label167
  addi x1, x1, 1
label167:
  beq  x2, x3, label168
  addi x1, x1, 1
label168:
  beq  x2, x3, label169
  addi x1, x1, 1
label169:
  beq  x2, x3, label170
  addi x1, x1, 1
label170:
  beq  x2, x3, label171
  addi x1, x1, 1
label171:
  beq  x2, x3, label172
  addi x1, x1, 1
label172:
  beq  x2, x3, label173
  addi x1, x1, 1
label173:
  beq  x2, x3, label174
  addi x1, x1, 1
label174:
  beq  x2, x3, label175
  addi x1, x1, 1
label175:
  beq  x2, x3, label176
  addi x1, x1, 1
label176:
  beq  x2, x3, label177
  addi x1, x1, 1
label177:
  beq  x2, x3, label178
  addi x1, x1, 1
label178:
  beq  x2, x3, label179
  addi x1, x1, 1
label179:
  beq  x2, x3, label180
  addi x1, x1, 1
label180:
  beq  x2, x3, label181
  addi x1, x1, 1
label181:
  beq  x2, x3, label182
  addi x1, x1, 1
label182:
  beq  x2, x3, label183
  addi x1, x1, 1
label183:
  beq  x2, x3, label184
  addi x1, x1, 1
label184:
  beq  x2, x3, label185
  addi x1, x1, 1
label185:
  beq  x2, x3, label186
  addi x1, x1, 1
label186:
  beq  x2, x3, label187
  addi x1, x1, 1
label187:
  beq  x2, x3, label188
  addi x1, x1, 1
label188:
  beq  x2, x3, label189
  addi x1, x1, 1
label189:
  beq  x2, x3, label190
  addi x1, x1, 1
label190:
  beq  x2, x3, label191
  addi x1, x1, 1
label191:
  beq  x2, x3, label192
  addi x1, x1, 1
label192:
  beq  x2, x3, label193
  addi x1, x1, 1
label193:
  beq  x2, x3, label194
  addi x1, x1, 1
label194:
  beq  x2, x3, label195
  addi x1, x1, 1
label195:
  beq  x2, x3, label196
  addi x1, x1, 1
label196:
  beq  x2, x3, label197
  addi x1, x1, 1
label197:
  beq  x2, x3, label198
  addi x1, x1, 1
label198:
  beq  x2, x3, label199
  addi x1, x1, 1
label199:
  beq  x2, x3, label200
  addi x1, x1, 1
label200:
  beq  x2, x3, label201
  addi x1, x1, 1
label201:
  beq  x2, x3, label202
  addi x1, x1, 1
label202:
  beq  x2, x3, label203
  addi x1, x1, 1
label203:
  beq  x2, x3, label204
  addi x1, x1, 1
label204:
  beq  x2, x3, label205
  addi x1, x1, 1
label205:
  beq  x2, x3, label206
  addi x1, x1, 1
label206:
  beq  x2, x3, label207
  addi x1, x1, 1
label207:
  beq  x2, x3, label208
  addi x1, x1, 1
label208:
  beq  x2, x3, label209
  addi x1, x1, 1
label209:
  beq  x2, x3, label210
  addi x1, x1, 1
label210:
  beq  x2, x3, label211
  addi x1, x1, 1
label211:
  beq  x2, x3, label212
  addi x1, x1, 1
label212:
  beq  x2, x3, label213
  addi x1, x1, 1
label213:
  beq  x2, x3, label214
  addi x1, x1, 1
label214:
  beq  x2, x3, label215
  addi x1, x1, 1
label215:
  beq  x2, x3, label216
  addi x1, x1, 1
label216:
  beq  x2, x3, label217
  addi x1, x1, 1
label217:
  beq  x2, x3, label218
  addi x1, x1, 1
label218:
  beq  x2, x3, label219
  addi x1, x1, 1
label219:
  beq  x2, x3, label220
  addi x1, x1, 1
label220:
  beq  x2, x3, label221
  addi x1, x1, 1
label221:
  beq  x2, x3, label222
  addi x1, x1, 1
label222:
  beq  x2, x3, label223
  addi x1, x1, 1
label223:
  beq  x2, x3, label224
  addi x1, x1, 1
label224:
  beq  x2, x3, label225
  addi x1, x1, 1
label225:
  beq  x2, x3, label226
  addi x1, x1, 1
label226:
  beq  x2, x3, label227
  addi x1, x1, 1
label227:
  beq  x2, x3, label228
  addi x1, x1, 1
label228:
  beq  x2, x3, label229
  addi x1, x1, 1
label229:
  beq  x2, x3, label230
  addi x1, x1, 1
label230:
  beq  x2, x3, label231
  addi x1, x1, 1
label231:
  beq  x2, x3, label232
  addi x1, x1, 1
label232:
  beq  x2, x3, label233
  addi x1, x1, 1
label233:
  beq  x2, x3, label234
  addi x1, x1, 1
label234:
  beq  x2, x3, label235
  addi x1, x1, 1
label235:
  beq  x2, x3, label236
  addi x1, x1, 1
label236:
  beq  x2, x3, label237
  addi x1, x1, 1
label237:
  beq  x2, x3, label238
  addi x1, x1, 1
label238:
  beq  x2, x3, label239
  addi x1, x1, 1
label239:
  beq  x2, x3, label240
  addi x1, x1, 1
label240:
  beq  x2, x3, label241
  addi x1, x1, 1
label241:
  beq  x2, x3, label242
  addi x1, x1, 1
label242:
  beq  x2, x3, label243
  addi x1, x1, 1
label243:
  beq  x2, x3, label244
  addi x1, x1, 1
label244:
  beq  x2, x3, label245
  addi x1, x1, 1
label245:
  beq  x2, x3, label246
  addi x1, x1, 1
label246:
  beq  x2, x3, label247
  addi x1, x1, 1
label247:
  beq  x2, x3, label248
  addi x1, x1, 1
label248:
  beq  x2, x3, label249
  addi x1, x1, 1
label249:
  beq  x2, x3, label250
  addi x1, x1, 1
label250:
  beq  x2, x3, label251
  addi x1, x1, 1
label251:
  beq  x2, x3, label252
  addi x1, x1, 1
label252:
  beq  x2, x3, label253
  addi x1, x1, 1
label253:
  beq  x2, x3, label254
  addi x1, x1, 1
label254:
  beq  x2, x3, label255
  addi x1, x1, 1
label255:
  beq  x2, x3, label256
  addi x1, x1, 1
label256:
  beq  x2, x3, label257
  addi x1, x1, 1
label257:
  beq  x2, x3, label258
  addi x1, x1, 1
label258:
  beq  x2, x3, label259
  addi x1, x1, 1
label259:
  beq  x2, x3, label260
  addi x1, x1, 1
label260:
  beq  x2, x3, label261
  addi x1, x1, 1
label261:
  beq  x2, x3, label262
  addi x1, x1, 1
label262:
  beq  x2, x3, label263
  addi x1, x1, 1
label263:
  beq  x2, x3, label264
  addi x1, x1, 1
label264:
  beq  x2, x3, label265
  addi x1, x1, 1
label265:
  beq  x2, x3, label266
  addi x1, x1, 1
label266:
  beq  x2, x3, label267
  addi x1, x1, 1
label267:
  beq  x2, x3, label268
  addi x1, x1, 1
label268:
  beq  x2, x3, label269
  addi x1, x1, 1
label269:
  beq  x2, x3, label270
  addi x1, x1, 1
label270:
  beq  x2, x3, label271
  addi x1, x1, 1
label271:
  beq  x2, x3, label272
  addi x1, x1, 1
label272:
  beq  x2, x3, label273
  addi x1, x1, 1
label273:
  beq  x2, x3, label274
  addi x1, x1, 1
label274:
  beq  x2, x3, label275
  addi x1, x1, 1
label275:
  beq  x2, x3, label276
  addi x1, x1, 1
label276:
  beq  x2, x3, label277
  addi x1, x1, 1
label277:
  beq  x2, x3, label278
  addi x1, x1, 1
label278:
  beq  x2, x3, label279
  addi x1, x1, 1
label279:
  beq  x2, x3, label280
  addi x1, x1, 1
label280:
  beq  x2, x3, label281
  addi x1, x1, 1
label281:
  beq  x2, x3, label282
  addi x1, x1, 1
label282:
  beq  x2, x3, label283
  addi x1, x1, 1
label283:
  beq  x2, x3, label284
  addi x1, x1, 1
label284:
  beq  x2, x3, label285
  addi x1, x1, 1
label285:
  beq  x2, x3, label286
  addi x1, x1, 1
label286:
  beq  x2, x3, label287
  addi x1, x1, 1
label287:
  beq  x2, x3, label288
  addi x1, x1, 1
label288:
  beq  x2, x3, label289
  addi x1, x1, 1
label289:
  beq  x2, x3, label290
  addi x1, x1, 1
label290:
  beq  x2, x3, label291
  addi x1, x1, 1
label291:
  beq  x2, x3, label292
  addi x1, x1, 1
label292:
  beq  x2, x3, label293
  addi x1, x1, 1
label293:
  beq  x2, x3, label294
  addi x1, x1, 1
label294:
  beq  x2, x3, label295
  addi x1, x1, 1
label295:
  beq  x2, x3, label296
  addi x1, x1, 1
label296:
  beq  x2, x3, label297
  addi x1, x1, 1
label297:
  beq  x2, x3, label298
  addi x1, x1, 1
label298:
  beq  x2, x3, label299
  addi x1, x1, 1
label299:
  beq  x2, x3, label300
  addi x1, x1, 1
label300:
  beq  x2, x3, label301
  addi x1, x1, 1
label301:
  beq  x2, x3, label302
  addi x1, x1, 1
label302:
  beq  x2, x3, label303
  addi x1, x1, 1
label303:
  beq  x2, x3, label304
  addi x1, x1, 1
label304:
  beq  x2, x3, label305
  addi x1, x1, 1
label305:
  beq  x2, x3, label306
  addi x1, x1, 1
label306:
  beq  x2, x3, label307
  addi x1, x1, 1
label307:
  beq  x2, x3, label308
  addi x1, x1, 1
label308:
  beq  x2, x3, label309
  addi x1, x1, 1
label309:
  beq  x2, x3, label310
  addi x1, x1, 1
label310:
  beq  x2, x3, label311
  addi x1, x1, 1
label311:
  beq  x2, x3, label312
  addi x1, x1, 1
label312:
  beq  x2, x3, label313
  addi x1, x1, 1
label313:
  beq  x2, x3, label314
  addi x1, x1, 1
label314:
  beq  x2, x3, label315
  addi x1, x1, 1
label315:
  beq  x2, x3, label316
  addi x1, x1, 1
label316:
  beq  x2, x3, label317
  addi x1, x1, 1
label317:
  beq  x2, x3, label318
  addi x1, x1, 1
label318:
  beq  x2, x3, label319
  addi x1, x1, 1
label319:
  beq  x2, x3, label320
  addi x1, x1, 1
label320:
  beq  x2, x3, label321
  addi x1, x1, 1
label321:
  beq  x2, x3, label322
  addi x1, x1, 1
label322:
  beq  x2, x3, label323
  addi x1, x1, 1
label323:
  beq  x2, x3, label324
  addi x1, x1, 1
label324:
  beq  x2, x3, label325
  addi x1, x1, 1
label325:
  beq  x2, x3, label326
  addi x1, x1, 1
label326:
  beq  x2, x3, label327
  addi x1, x1, 1
label327:
  beq  x2, x3, label328
  addi x1, x1, 1
label328:
  beq  x2, x3, label329
  addi x1, x1, 1
label329:
  beq  x2, x3, label330
  addi x1, x1, 1
label330:
  beq  x2, x3, label331
  addi x1, x1, 1
label331:
  beq  x2, x3, label332
  addi x1, x1, 1
label332:
  beq  x2, x3, label333
  addi x1, x1, 1
label333:
  beq  x2, x3, label334
  addi x1, x1, 1
label334:
  beq  x2, x3, label335
  addi x1, x1, 1
label335:
  beq  x2, x3, label336
  addi x1, x1, 1
label336:
  beq  x2, x3, label337
  addi x1, x1, 1
label337:
  beq  x2, x3, label338
  addi x1, x1, 1
label338:
  beq  x2, x3, label339
  addi x1, x1, 1
label339:
  beq  x2, x3, label340
  addi x1, x1, 1
label340:
  beq  x2, x3, label341
  addi x1, x1, 1
label341:
  beq  x2, x3, label342
  addi x1, x1, 1
label342:
  beq  x2, x3, label343
  addi x1, x1, 1
label343:
  beq  x2, x3, label344
  addi x1, x1, 1
label344:
  beq  x2, x3, label345
  addi x1, x1, 1
label345:
  beq  x2, x3, label346
  addi x1, x1, 1
label346:
  beq  x2, x3, label347
  addi x1, x1, 1
label347:
  beq  x2, x3, label348
  addi x1, x1, 1
label348:
  beq  x2, x3, label349
  addi x1, x1, 1
label349:
  beq  x2, x3, label350
  addi x1, x1, 1
label350:
  beq  x2, x3, label351
  addi x1, x1, 1
label351:
  beq  x2, x3, label352
  addi x1, x1, 1
label352:
  beq  x2, x3, label353
  addi x1, x1, 1
label353:
  beq  x2, x3, label354
  addi x1, x1, 1
label354:
  beq  x2, x3, label355
  addi x1, x1, 1
label355:
  beq  x2, x3, label356
  addi x1, x1, 1
label356:
  beq  x2, x3, label357
  addi x1, x1, 1
label357:
  beq  x2, x3, label358
  addi x1, x1, 1
label358:
  beq  x2, x3, label359
  addi x1, x1, 1
label359:
  beq  x2, x3, label360
  addi x1, x1, 1
label360:
  beq  x2, x3, label361
  addi x1, x1, 1
label361:
  beq  x2, x3, label362
  addi x1, x1, 1
label362:
  beq  x2, x3, label363
  addi x1, x1, 1
label363:
  beq  x2, x3, label364
  addi x1, x1, 1
label364:
  beq  x2, x3, label365
  addi x1, x1, 1
label365:
  beq  x2, x3, label366
  addi x1, x1, 1
label366:
  beq  x2, x3, label367
  addi x1, x1, 1
label367:
  beq  x2, x3, label368
  addi x1, x1, 1
label368:
  beq  x2, x3, label369
  addi x1, x1, 1
label369:
  beq  x2, x3, label370
  addi x1, x1, 1
label370:
  beq  x2, x3, label371
  addi x1, x1, 1
label371:
  beq  x2, x3, label372
  addi x1, x1, 1
label372:
  beq  x2, x3, label373
  addi x1, x1, 1
label373:
  beq  x2, x3, label374
  addi x1, x1, 1
label374:
  beq  x2, x3, label375
  addi x1, x1, 1
label375:
  beq  x2, x3, label376
  addi x1, x1, 1
label376:
  beq  x2, x3, label377
  addi x1, x1, 1
label377:
  beq  x2, x3, label378
  addi x1, x1, 1
label378:
  beq  x2, x3, label379
  addi x1, x1, 1
label379:
  beq  x2, x3, label380
  addi x1, x1, 1
label380:
  beq  x2, x3, label381
  addi x1, x1, 1
label381:
  beq  x2, x3, label382
  addi x1, x1, 1
label382:
  beq  x2, x3, label383
  addi x1, x1, 1
label383:
  beq  x2, x3, label384
  addi x1, x1, 1
label384:
  beq  x2, x3, label385
  addi x1, x1, 1
label385:
  beq  x2, x3, label386
  addi x1, x1, 1
label386:
  beq  x2, x3, label387
  addi x1, x1, 1
label387:
  beq  x2, x3, label388
  addi x1, x1, 1
label388:
  beq  x2, x3, label389
  addi x1, x1, 1
label389:
  beq  x2, x3, label390
  addi x1, x1, 1
label390:
  beq  x2, x3, label391
  addi x1, x1, 1
label391:
  beq  x2, x3, label392
  addi x1, x1, 1
label392:
  beq  x2, x3, label393
  addi x1, x1, 1
label393:
  beq  x2, x3, label394
  addi x1, x1, 1
label394:
  beq  x2, x3, label395
  addi x1, x1, 1
label395:
  beq  x2, x3, label396
  addi x1, x1, 1
label396:
  beq  x2, x3, label397
  addi x1, x1, 1
label397:
  beq  x2, x3, label398
  addi x1, x1, 1
label398:
  beq  x2, x3, label399
  addi x1, x1, 1
label399:
  beq  x2, x3, label400
  addi x1, x1, 1
label400:
  beq  x2, x3, label401
  addi x1, x1, 1
label401:
  beq  x2, x3, label402
  addi x1, x1, 1
label402:
  beq  x2, x3, label403
  addi x1, x1, 1
label403:
  beq  x2, x3, label404
  addi x1, x1, 1
label404:
  beq  x2, x3, label405
  addi x1, x1, 1
label405:
  beq  x2, x3, label406
  addi x1, x1, 1
label406:
  beq  x2, x3, label407
  addi x1, x1, 1
label407:
  beq  x2, x3, label408
  addi x1, x1, 1
label408:
  beq  x2, x3, label409
  addi x1, x1, 1
label409:
  beq  x2, x3, label410
  addi x1, x1, 1
label410:
  beq  x2, x3, label411
  addi x1, x1, 1
label411:
  beq  x2, x3, label412
  addi x1, x1, 1
label412:
  beq  x2, x3, label413
  addi x1, x1, 1
label413:
  beq  x2, x3, label414
  addi x1, x1, 1
label414:
  beq  x2, x3, label415
  addi x1, x1, 1
label415:
  beq  x2, x3, label416
  addi x1, x1, 1
label416:
  beq  x2, x3, label417
  addi x1, x1, 1
label417:
  beq  x2, x3, label418
  addi x1, x1, 1
label418:
  beq  x2, x3, label419
  addi x1, x1, 1
label419:
  beq  x2, x3, label420
  addi x1, x1, 1
label420:
  beq  x2, x3, label421
  addi x1, x1, 1
label421:
  beq  x2, x3, label422
  addi x1, x1, 1
label422:
  beq  x2, x3, label423
  addi x1, x1, 1
label423:
  beq  x2, x3, label424
  addi x1, x1, 1
label424:
  beq  x2, x3, label425
  addi x1, x1, 1
label425:
  beq  x2, x3, label426
  addi x1, x1, 1
label426:
  beq  x2, x3, label427
  addi x1, x1, 1
label427:
  beq  x2, x3, label428
  addi x1, x1, 1
label428:
  beq  x2, x3, label429
  addi x1, x1, 1
label429:
  beq  x2, x3, label430
  addi x1, x1, 1
label430:
  beq  x2, x3, label431
  addi x1, x1, 1
label431:
  beq  x2, x3, label432
  addi x1, x1, 1
label432:
  beq  x2, x3, label433
  addi x1, x1, 1
label433:
  beq  x2, x3, label434
  addi x1, x1, 1
label434:
  beq  x2, x3, label435
  addi x1, x1, 1
label435:
  beq  x2, x3, label436
  addi x1, x1, 1
label436:
  beq  x2, x3, label437
  addi x1, x1, 1
label437:
  beq  x2, x3, label438
  addi x1, x1, 1
label438:
  beq  x2, x3, label439
  addi x1, x1, 1
label439:
  beq  x2, x3, label440
  addi x1, x1, 1
label440:
  beq  x2, x3, label441
  addi x1, x1, 1
label441:
  beq  x2, x3, label442
  addi x1, x1, 1
label442:
  beq  x2, x3, label443
  addi x1, x1, 1
label443:
  beq  x2, x3, label444
  addi x1, x1, 1
label444:
  beq  x2, x3, label445
  addi x1, x1, 1
label445:
  beq  x2, x3, label446
  addi x1, x1, 1
label446:
  beq  x2, x3, label447
  addi x1, x1, 1
label447:
  beq  x2, x3, label448
  addi x1, x1, 1
label448:
  beq  x2, x3, label449
  addi x1, x1, 1
label449:
  beq  x2, x3, label450
  addi x1, x1, 1
label450:
  beq  x2, x3, label451
  addi x1, x1, 1
label451:
  beq  x2, x3, label452
  addi x1, x1, 1
label452:
  beq  x2, x3, label453
  addi x1, x1, 1
label453:
  beq  x2, x3, label454
  addi x1, x1, 1
label454:
  beq  x2, x3, label455
  addi x1, x1, 1
label455:
  beq  x2, x3, label456
  addi x1, x1, 1
label456:
  beq  x2, x3, label457
  addi x1, x1, 1
label457:
  beq  x2, x3, label458
  addi x1, x1, 1
label458:
  beq  x2, x3, label459
  addi x1, x1, 1
label459:
  beq  x2, x3, label460
  addi x1, x1, 1
label460:
  beq  x2, x3, label461
  addi x1, x1, 1
label461:
  beq  x2, x3, label462
  addi x1, x1, 1
label462:
  beq  x2, x3, label463
  addi x1, x1, 1
label463:
  beq  x2, x3, label464
  addi x1, x1, 1
label464:
  beq  x2, x3, label465
  addi x1, x1, 1
label465:
  beq  x2, x3, label466
  addi x1, x1, 1
label466:
  beq  x2, x3, label467
  addi x1, x1, 1
label467:
  beq  x2, x3, label468
  addi x1, x1, 1
label468:
  beq  x2, x3, label469
  addi x1, x1, 1
label469:
  beq  x2, x3, label470
  addi x1, x1, 1
label470:
  beq  x2, x3, label471
  addi x1, x1, 1
label471:
  beq  x2, x3, label472
  addi x1, x1, 1
label472:
  beq  x2, x3, label473
  addi x1, x1, 1
label473:
  beq  x2, x3, label474
  addi x1, x1, 1
label474:
  beq  x2, x3, label475
  addi x1, x1, 1
label475:
  beq  x2, x3, label476
  addi x1, x1, 1
label476:
  beq  x2, x3, label477
  addi x1, x1, 1
label477:
  beq  x2, x3, label478
  addi x1, x1, 1
label478:
  beq  x2, x3, label479
  addi x1, x1, 1
label479:
  beq  x2, x3, label480
  addi x1, x1, 1
label480:
  beq  x2, x3, label481
  addi x1, x1, 1
label481:
  beq  x2, x3, label482
  addi x1, x1, 1
label482:
  beq  x2, x3, label483
  addi x1, x1, 1
label483:
  beq  x2, x3, label484
  addi x1, x1, 1
label484:
  beq  x2, x3, label485
  addi x1, x1, 1
label485:
  beq  x2, x3, label486
  addi x1, x1, 1
label486:
  beq  x2, x3, label487
  addi x1, x1, 1
label487:
  beq  x2, x3, label488
  addi x1, x1, 1
label488:
  beq  x2, x3, label489
  addi x1, x1, 1
label489:
  beq  x2, x3, label490
  addi x1, x1, 1
label490:
  beq  x2, x3, label491
  addi x1, x1, 1
label491:
  beq  x2, x3, label492
  addi x1, x1, 1
label492:
  beq  x2, x3, label493
  addi x1, x1, 1
label493:
  beq  x2, x3, label494
  addi x1, x1, 1
label494:
  beq  x2, x3, label495
  addi x1, x1, 1
label495:
  beq  x2, x3, label496
  addi x1, x1, 1
label496:
  beq  x2, x3, label497
  addi x1, x1, 1
label497:
  beq  x2, x3, label498
  addi x1, x1, 1
label498:
  beq  x2, x3, label499
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
