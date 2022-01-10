/**
 * Simple description here
 *
 * @param a0 pointer to the buffer that will receive the version
 * @param a1 size of the buffer
 * @return 0 if ok
 */
  .globl get_version_1
  .type get_version_1, @function
  .option pic
  .option norvc
get_version_1:

  // Check src pointer is not NULL.
  beqz a0, L_get_version_1_nothing

  //compute the last address
  add a1, a0, a1

  lui a2, %hi(version_str_1)
  addi a2, a2, %lo(version_str_1)
L_get_version_1_loop:
  // Write the value into the section memory byte-by-byte.
  lb a3, 0(a2)
  beqz a3, L_get_version_1_end
  sb   a3, 0(a0)
  addi a0, a0, 1
  addi a2, a2, 1
  bltu a0, a1, L_get_version_1_loop

L_get_version_1_end:
  //Return 0
  li a0, 0
  ret

L_get_version_1_nothing:
  // Return -1
  li a0, -1
  ret

  // Set function size to allow disassembly.
  .size get_version_1, .-get_version_1

.global get_version_1_size
get_version_1_size:
  .4byte .-get_version_1

version_str_1:
  .string "V.1.23.12"


/**
 * Simple description here
 *
 * @param a0 pointer to the buffer that will receive the version
 * @param a1 size of the buffer
 * @return 0 if ok
 */
  .globl get_version_2
  .type get_version_2, @function
  .option pic
  .option norvc
get_version_2:

  // Check src pointer is not NULL.
  beqz a0, L_get_version_2_nothing

  //compute the last address
  add a1, a0, a1

  lui a2, %hi(version_str_2)
  addi a2, a2, %lo(version_str_2)
L_get_version_2_loop:
  // Write the value into the section memory byte-by-byte.
  lb a3, 0(a2)
  beqz a3, L_get_version_2_end
  sb   a3, 0(a0)
  addi a0, a0, 1
  addi a2, a2, 1
  bltu a0, a1, L_get_version_2_loop

L_get_version_2_end:
  //Return 0
  li a0, 0
  ret

L_get_version_2_nothing:
  // Return -1
  li a0, -1
  ret

  // Set function size to allow disassembly.
  .size get_version_2, .-get_version_2

.global get_version_2_size
get_version_2_size: 
  .4byte .-get_version_2

version_str_2:
  .string "V.2.00.00"