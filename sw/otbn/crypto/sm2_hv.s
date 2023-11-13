.globl sm2_pad
.globl sm2_compress
.globl sm2_hv
/*国家密码管理局批准的SM3密码杂凑算法，对长度为l(l < 2^64) 比特的消息m，SM3杂凑算法经过填充和迭代压缩，生成杂凑值，杂凑值长度
为256比特。*/

.text
/**
*假设消息m的长度为l比特。首先将比特“1”添加到消息的末尾，再添加k 个“0”，k是满
*足l + 1 + k ≡ 448mod512 的最小的非负整数。然后再添加一个64位比特串，该比特串是长度l的二进
*制表示。填充后的消息m′ 的比特长度为512的倍数。
*@param[in]  dmem[msg]: message to be signed (256 bits) 
**/
sm2_pad:
  /* Load message from dmem:
       w24 = msg <= dmem[msg] */
  la        x18, msg
  li        x2,  24
  bn.lid    x2, x18

  
/**
*SM3杂凑算法中的压缩函数
*令A,B,C,D,E,F,G,H为字寄存器,SS1,SS2,TT1,TT2为中间变量,压缩函数V
*i+1 = CF(V^(i), B(i)), 0 ≤i ≤ n−1。计算过程描述如下：
*ABCDEF GH ← V^(i)
*FOR j=0 TO 63
*    SS1 ← ((A ≪ 12) + E + (T_j ≪ j)) ≪ 7
*    SS2 ← SS1 ⊕ (A ≪ 12)
*    T T1 ← FF_j (A, B, C) + D + S S2 + W′_j
*    T T2 ← GG_j (E, F, G) + H + SS1 + W_j
*    D ← C
*    C ← B ≪ 9
*    B ← A
*    A ← T T1
*    H ← G
*    G ← F ≪ 19
*    F ← E
*    E ← P0(TT2)
*ENDFOR
*V^(i+1) ← ABCDEF GH ⊕ V^(i)
*其中，字的存储为大端(big-endian)格式。
*@param[in] 
**/
sm2_compress:

/**
* SM3杂凑算法
*
* @param [in]  dmem[msg]: message to be signed (256 bits)
**/
sm2_hv:













/* message digest */
.balign 32
.weak msg
msg:
  .zero 32

