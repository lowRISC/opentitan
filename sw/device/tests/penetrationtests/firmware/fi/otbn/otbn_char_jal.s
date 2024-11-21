/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR_JAL FI Penetration Test
*/
.section .text.start
  /* x1=counter. */
  li   x1, 0

  /* Try to hit a JAL instruction such that the branch is not taken.
     Then, the counter at the end is different to 0. */
  jal  x0, label0
  addi x1, x1, 1
label0:
  jal  x0, label1
  addi x1, x1, 1
label1:
  jal  x0, label2
  addi x1, x1, 1
label2:
  jal  x0, label3
  addi x1, x1, 1
label3:
  jal  x0, label4
  addi x1, x1, 1
label4:
  jal  x0, label5
  addi x1, x1, 1
label5:
  jal  x0, label6
  addi x1, x1, 1
label6:
  jal  x0, label7
  addi x1, x1, 1
label7:
  jal  x0, label8
  addi x1, x1, 1
label8:
  jal  x0, label9
  addi x1, x1, 1
label9:
  jal  x0, label10
  addi x1, x1, 1
label10:
  jal  x0, label11
  addi x1, x1, 1
label11:
  jal  x0, label12
  addi x1, x1, 1
label12:
  jal  x0, label13
  addi x1, x1, 1
label13:
  jal  x0, label14
  addi x1, x1, 1
label14:
  jal  x0, label15
  addi x1, x1, 1
label15:
  jal  x0, label16
  addi x1, x1, 1
label16:
  jal  x0, label17
  addi x1, x1, 1
label17:
  jal  x0, label18
  addi x1, x1, 1
label18:
  jal  x0, label19
  addi x1, x1, 1
label19:
  jal  x0, label20
  addi x1, x1, 1
label20:
  jal  x0, label21
  addi x1, x1, 1
label21:
  jal  x0, label22
  addi x1, x1, 1
label22:
  jal  x0, label23
  addi x1, x1, 1
label23:
  jal  x0, label24
  addi x1, x1, 1
label24:
  jal  x0, label25
  addi x1, x1, 1
label25:
  jal  x0, label26
  addi x1, x1, 1
label26:
  jal  x0, label27
  addi x1, x1, 1
label27:
  jal  x0, label28
  addi x1, x1, 1
label28:
  jal  x0, label29
  addi x1, x1, 1
label29:
  jal  x0, label30
  addi x1, x1, 1
label30:
  jal  x0, label31
  addi x1, x1, 1
label31:
  jal  x0, label32
  addi x1, x1, 1
label32:
  jal  x0, label33
  addi x1, x1, 1
label33:
  jal  x0, label34
  addi x1, x1, 1
label34:
  jal  x0, label35
  addi x1, x1, 1
label35:
  jal  x0, label36
  addi x1, x1, 1
label36:
  jal  x0, label37
  addi x1, x1, 1
label37:
  jal  x0, label38
  addi x1, x1, 1
label38:
  jal  x0, label39
  addi x1, x1, 1
label39:
  jal  x0, label40
  addi x1, x1, 1
label40:
  jal  x0, label41
  addi x1, x1, 1
label41:
  jal  x0, label42
  addi x1, x1, 1
label42:
  jal  x0, label43
  addi x1, x1, 1
label43:
  jal  x0, label44
  addi x1, x1, 1
label44:
  jal  x0, label45
  addi x1, x1, 1
label45:
  jal  x0, label46
  addi x1, x1, 1
label46:
  jal  x0, label47
  addi x1, x1, 1
label47:
  jal  x0, label48
  addi x1, x1, 1
label48:
  jal  x0, label49
  addi x1, x1, 1
label49:
  jal  x0, label50
  addi x1, x1, 1
label50:
  jal  x0, label51
  addi x1, x1, 1
label51:
  jal  x0, label52
  addi x1, x1, 1
label52:
  jal  x0, label53
  addi x1, x1, 1
label53:
  jal  x0, label54
  addi x1, x1, 1
label54:
  jal  x0, label55
  addi x1, x1, 1
label55:
  jal  x0, label56
  addi x1, x1, 1
label56:
  jal  x0, label57
  addi x1, x1, 1
label57:
  jal  x0, label58
  addi x1, x1, 1
label58:
  jal  x0, label59
  addi x1, x1, 1
label59:
  jal  x0, label60
  addi x1, x1, 1
label60:
  jal  x0, label61
  addi x1, x1, 1
label61:
  jal  x0, label62
  addi x1, x1, 1
label62:
  jal  x0, label63
  addi x1, x1, 1
label63:
  jal  x0, label64
  addi x1, x1, 1
label64:
  jal  x0, label65
  addi x1, x1, 1
label65:
  jal  x0, label66
  addi x1, x1, 1
label66:
  jal  x0, label67
  addi x1, x1, 1
label67:
  jal  x0, label68
  addi x1, x1, 1
label68:
  jal  x0, label69
  addi x1, x1, 1
label69:
  jal  x0, label70
  addi x1, x1, 1
label70:
  jal  x0, label71
  addi x1, x1, 1
label71:
  jal  x0, label72
  addi x1, x1, 1
label72:
  jal  x0, label73
  addi x1, x1, 1
label73:
  jal  x0, label74
  addi x1, x1, 1
label74:
  jal  x0, label75
  addi x1, x1, 1
label75:
  jal  x0, label76
  addi x1, x1, 1
label76:
  jal  x0, label77
  addi x1, x1, 1
label77:
  jal  x0, label78
  addi x1, x1, 1
label78:
  jal  x0, label79
  addi x1, x1, 1
label79:
  jal  x0, label80
  addi x1, x1, 1
label80:
  jal  x0, label81
  addi x1, x1, 1
label81:
  jal  x0, label82
  addi x1, x1, 1
label82:
  jal  x0, label83
  addi x1, x1, 1
label83:
  jal  x0, label84
  addi x1, x1, 1
label84:
  jal  x0, label85
  addi x1, x1, 1
label85:
  jal  x0, label86
  addi x1, x1, 1
label86:
  jal  x0, label87
  addi x1, x1, 1
label87:
  jal  x0, label88
  addi x1, x1, 1
label88:
  jal  x0, label89
  addi x1, x1, 1
label89:
  jal  x0, label90
  addi x1, x1, 1
label90:
  jal  x0, label91
  addi x1, x1, 1
label91:
  jal  x0, label92
  addi x1, x1, 1
label92:
  jal  x0, label93
  addi x1, x1, 1
label93:
  jal  x0, label94
  addi x1, x1, 1
label94:
  jal  x0, label95
  addi x1, x1, 1
label95:
  jal  x0, label96
  addi x1, x1, 1
label96:
  jal  x0, label97
  addi x1, x1, 1
label97:
  jal  x0, label98
  addi x1, x1, 1
label98:
  jal  x0, label99
  addi x1, x1, 1
label99:
  jal  x0, label100
  addi x1, x1, 1
label100:
  jal  x0, label101
  addi x1, x1, 1
label101:
  jal  x0, label102
  addi x1, x1, 1
label102:
  jal  x0, label103
  addi x1, x1, 1
label103:
  jal  x0, label104
  addi x1, x1, 1
label104:
  jal  x0, label105
  addi x1, x1, 1
label105:
  jal  x0, label106
  addi x1, x1, 1
label106:
  jal  x0, label107
  addi x1, x1, 1
label107:
  jal  x0, label108
  addi x1, x1, 1
label108:
  jal  x0, label109
  addi x1, x1, 1
label109:
  jal  x0, label110
  addi x1, x1, 1
label110:
  jal  x0, label111
  addi x1, x1, 1
label111:
  jal  x0, label112
  addi x1, x1, 1
label112:
  jal  x0, label113
  addi x1, x1, 1
label113:
  jal  x0, label114
  addi x1, x1, 1
label114:
  jal  x0, label115
  addi x1, x1, 1
label115:
  jal  x0, label116
  addi x1, x1, 1
label116:
  jal  x0, label117
  addi x1, x1, 1
label117:
  jal  x0, label118
  addi x1, x1, 1
label118:
  jal  x0, label119
  addi x1, x1, 1
label119:
  jal  x0, label120
  addi x1, x1, 1
label120:
  jal  x0, label121
  addi x1, x1, 1
label121:
  jal  x0, label122
  addi x1, x1, 1
label122:
  jal  x0, label123
  addi x1, x1, 1
label123:
  jal  x0, label124
  addi x1, x1, 1
label124:
  jal  x0, label125
  addi x1, x1, 1
label125:
  jal  x0, label126
  addi x1, x1, 1
label126:
  jal  x0, label127
  addi x1, x1, 1
label127:
  jal  x0, label128
  addi x1, x1, 1
label128:
  jal  x0, label129
  addi x1, x1, 1
label129:
  jal  x0, label130
  addi x1, x1, 1
label130:
  jal  x0, label131
  addi x1, x1, 1
label131:
  jal  x0, label132
  addi x1, x1, 1
label132:
  jal  x0, label133
  addi x1, x1, 1
label133:
  jal  x0, label134
  addi x1, x1, 1
label134:
  jal  x0, label135
  addi x1, x1, 1
label135:
  jal  x0, label136
  addi x1, x1, 1
label136:
  jal  x0, label137
  addi x1, x1, 1
label137:
  jal  x0, label138
  addi x1, x1, 1
label138:
  jal  x0, label139
  addi x1, x1, 1
label139:
  jal  x0, label140
  addi x1, x1, 1
label140:
  jal  x0, label141
  addi x1, x1, 1
label141:
  jal  x0, label142
  addi x1, x1, 1
label142:
  jal  x0, label143
  addi x1, x1, 1
label143:
  jal  x0, label144
  addi x1, x1, 1
label144:
  jal  x0, label145
  addi x1, x1, 1
label145:
  jal  x0, label146
  addi x1, x1, 1
label146:
  jal  x0, label147
  addi x1, x1, 1
label147:
  jal  x0, label148
  addi x1, x1, 1
label148:
  jal  x0, label149
  addi x1, x1, 1
label149:
  jal  x0, label150
  addi x1, x1, 1
label150:
  jal  x0, label151
  addi x1, x1, 1
label151:
  jal  x0, label152
  addi x1, x1, 1
label152:
  jal  x0, label153
  addi x1, x1, 1
label153:
  jal  x0, label154
  addi x1, x1, 1
label154:
  jal  x0, label155
  addi x1, x1, 1
label155:
  jal  x0, label156
  addi x1, x1, 1
label156:
  jal  x0, label157
  addi x1, x1, 1
label157:
  jal  x0, label158
  addi x1, x1, 1
label158:
  jal  x0, label159
  addi x1, x1, 1
label159:
  jal  x0, label160
  addi x1, x1, 1
label160:
  jal  x0, label161
  addi x1, x1, 1
label161:
  jal  x0, label162
  addi x1, x1, 1
label162:
  jal  x0, label163
  addi x1, x1, 1
label163:
  jal  x0, label164
  addi x1, x1, 1
label164:
  jal  x0, label165
  addi x1, x1, 1
label165:
  jal  x0, label166
  addi x1, x1, 1
label166:
  jal  x0, label167
  addi x1, x1, 1
label167:
  jal  x0, label168
  addi x1, x1, 1
label168:
  jal  x0, label169
  addi x1, x1, 1
label169:
  jal  x0, label170
  addi x1, x1, 1
label170:
  jal  x0, label171
  addi x1, x1, 1
label171:
  jal  x0, label172
  addi x1, x1, 1
label172:
  jal  x0, label173
  addi x1, x1, 1
label173:
  jal  x0, label174
  addi x1, x1, 1
label174:
  jal  x0, label175
  addi x1, x1, 1
label175:
  jal  x0, label176
  addi x1, x1, 1
label176:
  jal  x0, label177
  addi x1, x1, 1
label177:
  jal  x0, label178
  addi x1, x1, 1
label178:
  jal  x0, label179
  addi x1, x1, 1
label179:
  jal  x0, label180
  addi x1, x1, 1
label180:
  jal  x0, label181
  addi x1, x1, 1
label181:
  jal  x0, label182
  addi x1, x1, 1
label182:
  jal  x0, label183
  addi x1, x1, 1
label183:
  jal  x0, label184
  addi x1, x1, 1
label184:
  jal  x0, label185
  addi x1, x1, 1
label185:
  jal  x0, label186
  addi x1, x1, 1
label186:
  jal  x0, label187
  addi x1, x1, 1
label187:
  jal  x0, label188
  addi x1, x1, 1
label188:
  jal  x0, label189
  addi x1, x1, 1
label189:
  jal  x0, label190
  addi x1, x1, 1
label190:
  jal  x0, label191
  addi x1, x1, 1
label191:
  jal  x0, label192
  addi x1, x1, 1
label192:
  jal  x0, label193
  addi x1, x1, 1
label193:
  jal  x0, label194
  addi x1, x1, 1
label194:
  jal  x0, label195
  addi x1, x1, 1
label195:
  jal  x0, label196
  addi x1, x1, 1
label196:
  jal  x0, label197
  addi x1, x1, 1
label197:
  jal  x0, label198
  addi x1, x1, 1
label198:
  jal  x0, label199
  addi x1, x1, 1
label199:
  jal  x0, label200
  addi x1, x1, 1
label200:
  jal  x0, label201
  addi x1, x1, 1
label201:
  jal  x0, label202
  addi x1, x1, 1
label202:
  jal  x0, label203
  addi x1, x1, 1
label203:
  jal  x0, label204
  addi x1, x1, 1
label204:
  jal  x0, label205
  addi x1, x1, 1
label205:
  jal  x0, label206
  addi x1, x1, 1
label206:
  jal  x0, label207
  addi x1, x1, 1
label207:
  jal  x0, label208
  addi x1, x1, 1
label208:
  jal  x0, label209
  addi x1, x1, 1
label209:
  jal  x0, label210
  addi x1, x1, 1
label210:
  jal  x0, label211
  addi x1, x1, 1
label211:
  jal  x0, label212
  addi x1, x1, 1
label212:
  jal  x0, label213
  addi x1, x1, 1
label213:
  jal  x0, label214
  addi x1, x1, 1
label214:
  jal  x0, label215
  addi x1, x1, 1
label215:
  jal  x0, label216
  addi x1, x1, 1
label216:
  jal  x0, label217
  addi x1, x1, 1
label217:
  jal  x0, label218
  addi x1, x1, 1
label218:
  jal  x0, label219
  addi x1, x1, 1
label219:
  jal  x0, label220
  addi x1, x1, 1
label220:
  jal  x0, label221
  addi x1, x1, 1
label221:
  jal  x0, label222
  addi x1, x1, 1
label222:
  jal  x0, label223
  addi x1, x1, 1
label223:
  jal  x0, label224
  addi x1, x1, 1
label224:
  jal  x0, label225
  addi x1, x1, 1
label225:
  jal  x0, label226
  addi x1, x1, 1
label226:
  jal  x0, label227
  addi x1, x1, 1
label227:
  jal  x0, label228
  addi x1, x1, 1
label228:
  jal  x0, label229
  addi x1, x1, 1
label229:
  jal  x0, label230
  addi x1, x1, 1
label230:
  jal  x0, label231
  addi x1, x1, 1
label231:
  jal  x0, label232
  addi x1, x1, 1
label232:
  jal  x0, label233
  addi x1, x1, 1
label233:
  jal  x0, label234
  addi x1, x1, 1
label234:
  jal  x0, label235
  addi x1, x1, 1
label235:
  jal  x0, label236
  addi x1, x1, 1
label236:
  jal  x0, label237
  addi x1, x1, 1
label237:
  jal  x0, label238
  addi x1, x1, 1
label238:
  jal  x0, label239
  addi x1, x1, 1
label239:
  jal  x0, label240
  addi x1, x1, 1
label240:
  jal  x0, label241
  addi x1, x1, 1
label241:
  jal  x0, label242
  addi x1, x1, 1
label242:
  jal  x0, label243
  addi x1, x1, 1
label243:
  jal  x0, label244
  addi x1, x1, 1
label244:
  jal  x0, label245
  addi x1, x1, 1
label245:
  jal  x0, label246
  addi x1, x1, 1
label246:
  jal  x0, label247
  addi x1, x1, 1
label247:
  jal  x0, label248
  addi x1, x1, 1
label248:
  jal  x0, label249
  addi x1, x1, 1
label249:
  jal  x0, label250
  addi x1, x1, 1
label250:
  jal  x0, label251
  addi x1, x1, 1
label251:
  jal  x0, label252
  addi x1, x1, 1
label252:
  jal  x0, label253
  addi x1, x1, 1
label253:
  jal  x0, label254
  addi x1, x1, 1
label254:
  jal  x0, label255
  addi x1, x1, 1
label255:
  jal  x0, label256
  addi x1, x1, 1
label256:
  jal  x0, label257
  addi x1, x1, 1
label257:
  jal  x0, label258
  addi x1, x1, 1
label258:
  jal  x0, label259
  addi x1, x1, 1
label259:
  jal  x0, label260
  addi x1, x1, 1
label260:
  jal  x0, label261
  addi x1, x1, 1
label261:
  jal  x0, label262
  addi x1, x1, 1
label262:
  jal  x0, label263
  addi x1, x1, 1
label263:
  jal  x0, label264
  addi x1, x1, 1
label264:
  jal  x0, label265
  addi x1, x1, 1
label265:
  jal  x0, label266
  addi x1, x1, 1
label266:
  jal  x0, label267
  addi x1, x1, 1
label267:
  jal  x0, label268
  addi x1, x1, 1
label268:
  jal  x0, label269
  addi x1, x1, 1
label269:
  jal  x0, label270
  addi x1, x1, 1
label270:
  jal  x0, label271
  addi x1, x1, 1
label271:
  jal  x0, label272
  addi x1, x1, 1
label272:
  jal  x0, label273
  addi x1, x1, 1
label273:
  jal  x0, label274
  addi x1, x1, 1
label274:
  jal  x0, label275
  addi x1, x1, 1
label275:
  jal  x0, label276
  addi x1, x1, 1
label276:
  jal  x0, label277
  addi x1, x1, 1
label277:
  jal  x0, label278
  addi x1, x1, 1
label278:
  jal  x0, label279
  addi x1, x1, 1
label279:
  jal  x0, label280
  addi x1, x1, 1
label280:
  jal  x0, label281
  addi x1, x1, 1
label281:
  jal  x0, label282
  addi x1, x1, 1
label282:
  jal  x0, label283
  addi x1, x1, 1
label283:
  jal  x0, label284
  addi x1, x1, 1
label284:
  jal  x0, label285
  addi x1, x1, 1
label285:
  jal  x0, label286
  addi x1, x1, 1
label286:
  jal  x0, label287
  addi x1, x1, 1
label287:
  jal  x0, label288
  addi x1, x1, 1
label288:
  jal  x0, label289
  addi x1, x1, 1
label289:
  jal  x0, label290
  addi x1, x1, 1
label290:
  jal  x0, label291
  addi x1, x1, 1
label291:
  jal  x0, label292
  addi x1, x1, 1
label292:
  jal  x0, label293
  addi x1, x1, 1
label293:
  jal  x0, label294
  addi x1, x1, 1
label294:
  jal  x0, label295
  addi x1, x1, 1
label295:
  jal  x0, label296
  addi x1, x1, 1
label296:
  jal  x0, label297
  addi x1, x1, 1
label297:
  jal  x0, label298
  addi x1, x1, 1
label298:
  jal  x0, label299
  addi x1, x1, 1
label299:
  jal  x0, label300
  addi x1, x1, 1
label300:
  jal  x0, label301
  addi x1, x1, 1
label301:
  jal  x0, label302
  addi x1, x1, 1
label302:
  jal  x0, label303
  addi x1, x1, 1
label303:
  jal  x0, label304
  addi x1, x1, 1
label304:
  jal  x0, label305
  addi x1, x1, 1
label305:
  jal  x0, label306
  addi x1, x1, 1
label306:
  jal  x0, label307
  addi x1, x1, 1
label307:
  jal  x0, label308
  addi x1, x1, 1
label308:
  jal  x0, label309
  addi x1, x1, 1
label309:
  jal  x0, label310
  addi x1, x1, 1
label310:
  jal  x0, label311
  addi x1, x1, 1
label311:
  jal  x0, label312
  addi x1, x1, 1
label312:
  jal  x0, label313
  addi x1, x1, 1
label313:
  jal  x0, label314
  addi x1, x1, 1
label314:
  jal  x0, label315
  addi x1, x1, 1
label315:
  jal  x0, label316
  addi x1, x1, 1
label316:
  jal  x0, label317
  addi x1, x1, 1
label317:
  jal  x0, label318
  addi x1, x1, 1
label318:
  jal  x0, label319
  addi x1, x1, 1
label319:
  jal  x0, label320
  addi x1, x1, 1
label320:
  jal  x0, label321
  addi x1, x1, 1
label321:
  jal  x0, label322
  addi x1, x1, 1
label322:
  jal  x0, label323
  addi x1, x1, 1
label323:
  jal  x0, label324
  addi x1, x1, 1
label324:
  jal  x0, label325
  addi x1, x1, 1
label325:
  jal  x0, label326
  addi x1, x1, 1
label326:
  jal  x0, label327
  addi x1, x1, 1
label327:
  jal  x0, label328
  addi x1, x1, 1
label328:
  jal  x0, label329
  addi x1, x1, 1
label329:
  jal  x0, label330
  addi x1, x1, 1
label330:
  jal  x0, label331
  addi x1, x1, 1
label331:
  jal  x0, label332
  addi x1, x1, 1
label332:
  jal  x0, label333
  addi x1, x1, 1
label333:
  jal  x0, label334
  addi x1, x1, 1
label334:
  jal  x0, label335
  addi x1, x1, 1
label335:
  jal  x0, label336
  addi x1, x1, 1
label336:
  jal  x0, label337
  addi x1, x1, 1
label337:
  jal  x0, label338
  addi x1, x1, 1
label338:
  jal  x0, label339
  addi x1, x1, 1
label339:
  jal  x0, label340
  addi x1, x1, 1
label340:
  jal  x0, label341
  addi x1, x1, 1
label341:
  jal  x0, label342
  addi x1, x1, 1
label342:
  jal  x0, label343
  addi x1, x1, 1
label343:
  jal  x0, label344
  addi x1, x1, 1
label344:
  jal  x0, label345
  addi x1, x1, 1
label345:
  jal  x0, label346
  addi x1, x1, 1
label346:
  jal  x0, label347
  addi x1, x1, 1
label347:
  jal  x0, label348
  addi x1, x1, 1
label348:
  jal  x0, label349
  addi x1, x1, 1
label349:
  jal  x0, label350
  addi x1, x1, 1
label350:
  jal  x0, label351
  addi x1, x1, 1
label351:
  jal  x0, label352
  addi x1, x1, 1
label352:
  jal  x0, label353
  addi x1, x1, 1
label353:
  jal  x0, label354
  addi x1, x1, 1
label354:
  jal  x0, label355
  addi x1, x1, 1
label355:
  jal  x0, label356
  addi x1, x1, 1
label356:
  jal  x0, label357
  addi x1, x1, 1
label357:
  jal  x0, label358
  addi x1, x1, 1
label358:
  jal  x0, label359
  addi x1, x1, 1
label359:
  jal  x0, label360
  addi x1, x1, 1
label360:
  jal  x0, label361
  addi x1, x1, 1
label361:
  jal  x0, label362
  addi x1, x1, 1
label362:
  jal  x0, label363
  addi x1, x1, 1
label363:
  jal  x0, label364
  addi x1, x1, 1
label364:
  jal  x0, label365
  addi x1, x1, 1
label365:
  jal  x0, label366
  addi x1, x1, 1
label366:
  jal  x0, label367
  addi x1, x1, 1
label367:
  jal  x0, label368
  addi x1, x1, 1
label368:
  jal  x0, label369
  addi x1, x1, 1
label369:
  jal  x0, label370
  addi x1, x1, 1
label370:
  jal  x0, label371
  addi x1, x1, 1
label371:
  jal  x0, label372
  addi x1, x1, 1
label372:
  jal  x0, label373
  addi x1, x1, 1
label373:
  jal  x0, label374
  addi x1, x1, 1
label374:
  jal  x0, label375
  addi x1, x1, 1
label375:
  jal  x0, label376
  addi x1, x1, 1
label376:
  jal  x0, label377
  addi x1, x1, 1
label377:
  jal  x0, label378
  addi x1, x1, 1
label378:
  jal  x0, label379
  addi x1, x1, 1
label379:
  jal  x0, label380
  addi x1, x1, 1
label380:
  jal  x0, label381
  addi x1, x1, 1
label381:
  jal  x0, label382
  addi x1, x1, 1
label382:
  jal  x0, label383
  addi x1, x1, 1
label383:
  jal  x0, label384
  addi x1, x1, 1
label384:
  jal  x0, label385
  addi x1, x1, 1
label385:
  jal  x0, label386
  addi x1, x1, 1
label386:
  jal  x0, label387
  addi x1, x1, 1
label387:
  jal  x0, label388
  addi x1, x1, 1
label388:
  jal  x0, label389
  addi x1, x1, 1
label389:
  jal  x0, label390
  addi x1, x1, 1
label390:
  jal  x0, label391
  addi x1, x1, 1
label391:
  jal  x0, label392
  addi x1, x1, 1
label392:
  jal  x0, label393
  addi x1, x1, 1
label393:
  jal  x0, label394
  addi x1, x1, 1
label394:
  jal  x0, label395
  addi x1, x1, 1
label395:
  jal  x0, label396
  addi x1, x1, 1
label396:
  jal  x0, label397
  addi x1, x1, 1
label397:
  jal  x0, label398
  addi x1, x1, 1
label398:
  jal  x0, label399
  addi x1, x1, 1
label399:
  jal  x0, label400
  addi x1, x1, 1
label400:
  jal  x0, label401
  addi x1, x1, 1
label401:
  jal  x0, label402
  addi x1, x1, 1
label402:
  jal  x0, label403
  addi x1, x1, 1
label403:
  jal  x0, label404
  addi x1, x1, 1
label404:
  jal  x0, label405
  addi x1, x1, 1
label405:
  jal  x0, label406
  addi x1, x1, 1
label406:
  jal  x0, label407
  addi x1, x1, 1
label407:
  jal  x0, label408
  addi x1, x1, 1
label408:
  jal  x0, label409
  addi x1, x1, 1
label409:
  jal  x0, label410
  addi x1, x1, 1
label410:
  jal  x0, label411
  addi x1, x1, 1
label411:
  jal  x0, label412
  addi x1, x1, 1
label412:
  jal  x0, label413
  addi x1, x1, 1
label413:
  jal  x0, label414
  addi x1, x1, 1
label414:
  jal  x0, label415
  addi x1, x1, 1
label415:
  jal  x0, label416
  addi x1, x1, 1
label416:
  jal  x0, label417
  addi x1, x1, 1
label417:
  jal  x0, label418
  addi x1, x1, 1
label418:
  jal  x0, label419
  addi x1, x1, 1
label419:
  jal  x0, label420
  addi x1, x1, 1
label420:
  jal  x0, label421
  addi x1, x1, 1
label421:
  jal  x0, label422
  addi x1, x1, 1
label422:
  jal  x0, label423
  addi x1, x1, 1
label423:
  jal  x0, label424
  addi x1, x1, 1
label424:
  jal  x0, label425
  addi x1, x1, 1
label425:
  jal  x0, label426
  addi x1, x1, 1
label426:
  jal  x0, label427
  addi x1, x1, 1
label427:
  jal  x0, label428
  addi x1, x1, 1
label428:
  jal  x0, label429
  addi x1, x1, 1
label429:
  jal  x0, label430
  addi x1, x1, 1
label430:
  jal  x0, label431
  addi x1, x1, 1
label431:
  jal  x0, label432
  addi x1, x1, 1
label432:
  jal  x0, label433
  addi x1, x1, 1
label433:
  jal  x0, label434
  addi x1, x1, 1
label434:
  jal  x0, label435
  addi x1, x1, 1
label435:
  jal  x0, label436
  addi x1, x1, 1
label436:
  jal  x0, label437
  addi x1, x1, 1
label437:
  jal  x0, label438
  addi x1, x1, 1
label438:
  jal  x0, label439
  addi x1, x1, 1
label439:
  jal  x0, label440
  addi x1, x1, 1
label440:
  jal  x0, label441
  addi x1, x1, 1
label441:
  jal  x0, label442
  addi x1, x1, 1
label442:
  jal  x0, label443
  addi x1, x1, 1
label443:
  jal  x0, label444
  addi x1, x1, 1
label444:
  jal  x0, label445
  addi x1, x1, 1
label445:
  jal  x0, label446
  addi x1, x1, 1
label446:
  jal  x0, label447
  addi x1, x1, 1
label447:
  jal  x0, label448
  addi x1, x1, 1
label448:
  jal  x0, label449
  addi x1, x1, 1
label449:
  jal  x0, label450
  addi x1, x1, 1
label450:
  jal  x0, label451
  addi x1, x1, 1
label451:
  jal  x0, label452
  addi x1, x1, 1
label452:
  jal  x0, label453
  addi x1, x1, 1
label453:
  jal  x0, label454
  addi x1, x1, 1
label454:
  jal  x0, label455
  addi x1, x1, 1
label455:
  jal  x0, label456
  addi x1, x1, 1
label456:
  jal  x0, label457
  addi x1, x1, 1
label457:
  jal  x0, label458
  addi x1, x1, 1
label458:
  jal  x0, label459
  addi x1, x1, 1
label459:
  jal  x0, label460
  addi x1, x1, 1
label460:
  jal  x0, label461
  addi x1, x1, 1
label461:
  jal  x0, label462
  addi x1, x1, 1
label462:
  jal  x0, label463
  addi x1, x1, 1
label463:
  jal  x0, label464
  addi x1, x1, 1
label464:
  jal  x0, label465
  addi x1, x1, 1
label465:
  jal  x0, label466
  addi x1, x1, 1
label466:
  jal  x0, label467
  addi x1, x1, 1
label467:
  jal  x0, label468
  addi x1, x1, 1
label468:
  jal  x0, label469
  addi x1, x1, 1
label469:
  jal  x0, label470
  addi x1, x1, 1
label470:
  jal  x0, label471
  addi x1, x1, 1
label471:
  jal  x0, label472
  addi x1, x1, 1
label472:
  jal  x0, label473
  addi x1, x1, 1
label473:
  jal  x0, label474
  addi x1, x1, 1
label474:
  jal  x0, label475
  addi x1, x1, 1
label475:
  jal  x0, label476
  addi x1, x1, 1
label476:
  jal  x0, label477
  addi x1, x1, 1
label477:
  jal  x0, label478
  addi x1, x1, 1
label478:
  jal  x0, label479
  addi x1, x1, 1
label479:
  jal  x0, label480
  addi x1, x1, 1
label480:
  jal  x0, label481
  addi x1, x1, 1
label481:
  jal  x0, label482
  addi x1, x1, 1
label482:
  jal  x0, label483
  addi x1, x1, 1
label483:
  jal  x0, label484
  addi x1, x1, 1
label484:
  jal  x0, label485
  addi x1, x1, 1
label485:
  jal  x0, label486
  addi x1, x1, 1
label486:
  jal  x0, label487
  addi x1, x1, 1
label487:
  jal  x0, label488
  addi x1, x1, 1
label488:
  jal  x0, label489
  addi x1, x1, 1
label489:
  jal  x0, label490
  addi x1, x1, 1
label490:
  jal  x0, label491
  addi x1, x1, 1
label491:
  jal  x0, label492
  addi x1, x1, 1
label492:
  jal  x0, label493
  addi x1, x1, 1
label493:
  jal  x0, label494
  addi x1, x1, 1
label494:
  jal  x0, label495
  addi x1, x1, 1
label495:
  jal  x0, label496
  addi x1, x1, 1
label496:
  jal  x0, label497
  addi x1, x1, 1
label497:
  jal  x0, label498
  addi x1, x1, 1
label498:
  jal  x0, label499
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
