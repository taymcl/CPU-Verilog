//********** REGFILE MODULE **********
// modified register file to use 16 bits
module reg_file (rr1,rr2,wr,wd,regwrite,rd1,rd2,clock);
  input [1:0] rr1,rr2,wr;
  input [15:0] wd;
  input regwrite,clock;
  output [15:0] rd1,rd2;
  reg [15:0] Regs[0:3];
  assign rd1 = Regs[rr1];
  assign rd2 = Regs[rr2];
  initial Regs[0] = 0;
  always @(negedge clock)
    if (regwrite==1 & wr!=0)
     Regs[wr] <= wd;
endmodule

//**************Multiplexors******************
module mux4x1(i0,i1,i2,i3,select,y);
  input i0,i1,i2,i3;
  input [1:0] select;
  output y;
  mux2x1 mux1(i0, i1, select[0], m1);
  mux2x1 mux2(i2, i3, select[0], m2);
  mux2x1 mux3(m1, m2, select[1], y);
endmodule

//used by WR
module mux2bit2x1(A,B,select,OUT);
  input [1:0] A,B;
  input select;
  output [1:0] OUT;
  //cascade 2 2x1 muxs
  mux2x1 mux1(A[0], B[0], select, OUT[0]),
  mux2(A[1], B[1], select, OUT[1]);
endmodule

//used by WD, B, Branch
module mux2x1_16bit(A, B, select, OUT);
  input [15:0] A,B;
  input select;
  output [15:0] OUT;
  //cascade 16 2x1 mux's
  mux2x1 mux1(A[0], B[0], select, OUT[0]),
  mux2(A[1], B[1], select, OUT[1]),
  mux3(A[2], B[2], select, OUT[2]),
  mux4(A[3], B[3], select, OUT[3]),
  mux5(A[4], B[4], select, OUT[4]),
  mux6(A[5], B[5], select, OUT[5]),
  mux7(A[6], B[6], select, OUT[6]),
  mux8(A[7], B[7], select, OUT[7]),
  mux9(A[8], B[8], select, OUT[8]),
  mux10(A[9], B[9], select, OUT[9]),
  mux11(A[10], B[10], select, OUT[10]),
  mux12(A[11], B[11], select, OUT[11]),
  mux13(A[12], B[12], select, OUT[12]),
  mux14(A[13], B[13], select, OUT[13]),
  mux15(A[14], B[14], select, OUT[14]),
  mux16(A[15], B[15], select, OUT[15]);
endmodule
//********** END OF REGFILE MODULES **********
//********** ALU MODULES **********
// 16-bit MIPS ALU in Verilog using modified template of 4-bit ALU
module ALU (op,a,b,result,zero);
  input [15:0] a; //16 bit inputs a,b
  input [15:0] b;
  input [2:0] op; //3 bit alu opp code
  output [15:0] result; // produce 16 bit output
  output zero;
  wire c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16;
  //cascade 16 single bit alu's
    ALU1 alu0 (a[0], b[0], op[2], op[1:0],set,op[2],c1,result[0]);
    ALU1 alu1 (a[1], b[1], op[2], op[1:0], 1'b0, c1, c2,result[1]);
    ALU1 alu2 (a[2], b[2], op[2], op[1:0], 1'b0, c2, c3,result[2]);
    ALU1 alu3 (a[3], b[3], op[2], op[1:0], 1'b0, c3, c4,result[3]);
    ALU1 alu4 (a[4], b[4], op[2], op[1:0], 1'b0, c4, c5,result[4]);
    ALU1 alu5 (a[5], b[5], op[2], op[1:0], 1'b0, c5, c6,result[5]);
    ALU1 alu6 (a[6], b[6], op[2], op[1:0], 1'b0, c6, c7,result[6]);
    ALU1 alu7 (a[7], b[7], op[2], op[1:0], 1'b0, c7, c8,result[7]);
    ALU1 alu8 (a[8], b[8], op[2], op[1:0], 1'b0, c8, c9,result[8]);
    ALU1 alu9 (a[9], b[9], op[2], op[1:0], 1'b0, c9, c10,result[9]);
    ALU1 alu10 (a[10],b[10],op[2], op[1:0], 1'b0, c10, c11,result[10]);
    ALU1 alu11 (a[11],b[11],op[2], op[1:0], 1'b0, c11, c12,result[11]);
    ALU1 alu12 (a[12],b[12],op[2], op[1:0], 1'b0, c12, c13,result[12]);
    ALU1 alu13 (a[13],b[13],op[2], op[1:0], 1'b0, c13, c14,result[13]);
    ALU1 alu14 (a[14],b[14],op[2], op[1:0], 1'b0, c14, c15,result[14]);
    ALUmsb alu15 (a[15],b[15],op[2], op[1:0], 1'b0, c15, c16,result[15],set);
    or or1(or01, result[0],result[1]);
    or or2(or23, result[2],result[3]);
    nor nor1(zero,or01,or23);
endmodule

// 1-bit ALU for bits 0-2
module ALU1 (a,b,binvert,op,less,carryin,carryout,result);
  input a,b,less,carryin,binvert;
  input [1:0] op;
  output carryout,result;
  wire sum, a_and_b, a_or_b, b_inv;
  not not1(b_inv, b);
  mux2x1 mux1(b,b_inv,binvert,b1);
  and and1(a_and_b, a, b);
  or or1(a_or_b, a, b);
  fulladder adder1(sum,carryout,a,b1,carryin);
  mux4x1 mux2(a_and_b,a_or_b,sum,less,op[1:0],result);
endmodule

// 1-bit ALU for the most significant bit
module ALUmsb (a,b,binvert,op,less,carryin,carryout,result,sum);
  input a,b,less,carryin,binvert;
  input [1:0] op;
  output carryout,result,sum;
  wire sum, a_and_b, a_or_b, b_inv;
  not not1(b_inv, b);
  mux2x1 mux1(b,b_inv,binvert,b1);
  and and1(a_and_b, a, b);
  or or1(a_or_b, a, b);
  fulladder adder1(sum,carryout,a,b1,carryin);
  mux4x1 mux2(a_and_b,a_or_b,sum,less,op[1:0],result);
endmodule

module halfadder (S,C,x,y);
  input x,y;
  output S,C;
  xor (S,x,y);
  and (C,x,y);
endmodule

module fulladder (S,C,x,y,z);
  input x,y,z;
  output S,C;
  wire S1,D1,D2;
  halfadder HA1 (S1,D1,x,y),
  HA2 (S,D2,S1,z);
  or g1(C,D2,D1);
endmodule

module mux2x1(A,B,select,OUT);
  input A,B,select;
  output OUT;
  not not1(i0, select);
  and and1(i1, A, i0);
  and and2(i2, B, select);
  or or1(OUT, i1, i2);
endmodule
//********** END OF ALU MODULES **********
//********** CONTROL MODULES **********
module MainControl (Op, Control);
  input [3:0] Op;
  // RegDst[1], AluSrc[1], MemtoReg[1], RegWrite[1], MemWrite1[1], BEQ[1], BNE[1], AluCtrl[3]
  output reg [9:0] Control;
  always @(Op) case (Op)
    4'b0000: Control <= 10'b1001000010; //add
    4'b0001: Control <= 10'b1001000110; //sub
    4'b0010: Control <= 10'b1001000000; //and
    4'b0011: Control <= 10'b1001000001; //or
    4'b0111: Control <= 10'b1001000111; //slt
    4'b0101: Control <= 10'b0111000010; //lw
    4'b0110: Control <= 10'b0100100010; //sw
    4'b1000: Control <= 10'b0000001110; //beq
    4'b1001: Control <= 10'b0000010110; //bne
    4'b0100: Control <= 10'b0101000010; //addi
  endcase
endmodule

module BranchControl (BranchOp,Zero,BranchOut);
  input [1:0] BranchOp; // two bits to handle bne/beq
  input Zero;
  output BranchOut;
  wire ZeroInvert,i0,i1;
  not not1(ZeroInvert,Zero);
  and and1(i0,BranchOp[0],Zero);
  and and2(i1,BranchOp[1],ZeroInvert);
  or or1(BranchOut,i0,i1);
endmodule

//********** END OF CONTROL MODULES **********
//********** CPU **********
// CPU template modified from "mips-pipe3.vl"
module CPU (clock,PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
  input clock;
  output [15:0] PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD;
  initial begin
    // Program: swap memory cells (if needed) and compute absolute value |5-7|=2
    IMemory[0] = 16'b0101_00_01_00000000; // lw $1, 0($0)
    IMemory[1] = 16'b0101_00_10_00000010; // lw $2, 2($0)
    IMemory[2] = 16'b0000_00_00_00000000; // nop
    IMemory[3] = 16'b0000_00_00_00000000; // nop
    IMemory[4] = 16'b0000_00_00_00000000; // nop
    IMemory[5] = 16'b0111_01_10_11_000000; // slt $3, $1, $2
    IMemory[6] = 16'b0000_00_00_00000000; // nop
    IMemory[7] = 16'b0000_00_00_00000000; // nop
    IMemory[8] = 16'b0000_00_00_00000000; // nop
    IMemory[9] = 16'b1000_00_11_00000101; // beq $3, $0, IMemory[5]
    IMemory[10] = 16'b0000_00_00_00000000; // nop
    IMemory[11] = 16'b0000_00_00_00000000; // nop
    IMemory[12] = 16'b0000_00_00_00000000; // nop
    IMemory[13] = 16'b0110_00_01_00000010; // sw $1, 2($0)
    IMemory[14] = 16'b0110_00_10_00000000; // sw $2, 0($0)
    IMemory[15] = 16'b0000_00_00_00000000; // nop
    IMemory[16] = 16'b0000_00_00_00000000; // nop
    IMemory[17] = 16'b0000_00_00_00000000; // nop
    IMemory[18] = 16'b0101_00_01_00000000; // lw $1, 0($0)
    IMemory[19] = 16'b0101_00_10_00000010; // lw $2, 2($0)
    IMemory[20] = 16'b0000_00_00_00000000; // nop
    IMemory[21] = 16'b0000_00_00_00000000; // nop
    IMemory[22] = 16'b0000_00_00_00000000; // nop
    IMemory[23] = 16'b001_01_10_11_000000; // sub $3, $1, $2
    // Data
    DMemory [0] = 32'h5; // switch the cells and see how the simulation output changes
    DMemory [1] = 32'h7; // (beq is taken if [0]=32'h7; [1]=32'h5, not taken otherwise)
  end
// Pipeline stages
//IF
  wire [15:0] NextPC,PCplus2;
  reg [15:0] PC, IMemory[0:1023], IFID_IR,IFID_PCplus2;
  ALU fetch (3'b010,PC,16'b10,PCplus2,Unused); //play with timings here
  BranchControl BranchCtrl (EXMEM_Branch,EXMEM_Zero,BranchConOut); // added branch control
  mux2x1_16bit BranchMux (PCplus2,EXMEM_Target,BranchConOut,NextPC); // added mux for branch
//ID
  reg [15:0] IDEX_IR; // For monitoring the pipeline
  wire [9:0] Control;
  reg IDEX_RegWrite,IDEX_ALUSrc,IDEX_RegDst,IDEX_MemtoReg,IDEX_MemWrite;
  reg [1:0] IDEX_Branch; // because our bne and bqe are 2 bits
  reg [2:0] IDEX_ALUOp; // our aluOps are 3 bits
  wire [15:0] RD1,RD2,SignExtend, WD;
  reg [15:0] IDEX_RD1,IDEX_RD2,IDEX_SignExt,IDEX_PCplus2,IDEXE_IR; // added IDEX_PCplus2,IDEXE_IR
  reg [1:0] IDEX_rt,IDEX_rd; //should be 2 bit
  reg MEMWB_RegWrite; // part of MEM stage, but declared here before use (to avoid error)
  reg [1:0] MEMWB_rd; // part of MEM stage, but declared here before use (to avoid error) reg_file rf
  (IFID_IR[11:10],IFID_IR[9:8],MEMWB_rd,WD,MEMWB_RegWrite,RD1,RD2,clock); //added MEMWB_rd & MEMWB_RegWrite
  MainControl MainCtr (IFID_IR[15:12],Control);
  assign SignExtend = {{8{IFID_IR[7]}},IFID_IR[7:0]};
//EXE
  reg EXMEM_RegWrite,EXMEM_MemtoReg,EXMEM_MemWrite;
  reg [1:0] EXMEM_Branch;
  wire [15:0] Target;
  reg EXMEM_Zero;
  reg [15:0] EXMEM_Target,EXMEM_ALUOut,EXMEM_RD2;
  reg [15:0] EXMEM_IR; // this is for monitoring the pipeline
  reg [1:0] EXMEM_rd;
  wire [15:0] B,ALUOut;
  wire [1:0] WR;
  ALU branch (3'b010,IDEX_SignExt<<1,IDEX_PCplus2,Target,Unused2);
  ALU ex (IDEX_ALUOp, IDEX_RD1, B, ALUOut, Zero);
  mux2bit2x1 RegDstMux (IDEX_rt, IDEX_rd, IDEX_RegDst, WR); // assign WR, Reg Dst mux
  mux2x1_16bit ALUSrcMux (IDEX_RD2, IDEX_SignExt, IDEX_ALUSrc, B); // assign B, ALU src mux
//MEM
  reg MEMWB_MemtoReg;
  reg [15:0] DMemory[0:1023],MEMWB_MemOut,MEMWB_ALUOut;
  reg [15:0] MEMWB_IR; // For monitoring the pipeline
  wire [15:0] MemOut;
  assign MemOut = DMemory[EXMEM_ALUOut>>1];
  always @(negedge clock) if (EXMEM_MemWrite) DMemory[EXMEM_ALUOut>>1] <=EXMEM_RD2;
//WB  
  mux2x1_16bit MemToReg (MEMWB_ALUOut, MEMWB_MemOut, MEMWB_MemtoReg, WD); // MemtoReg Mux
 initial begin
  PC = 0;
// Initialize pipeline registers
  IDEX_RegWrite=0;IDEX_MemtoReg=0;IDEX_Branch=0;IDEX_MemWrite=0;IDEX_ALUSrc=0;IDEX_RegDst=0;IDEX_ALUOp=0;
  IFID_IR=0;
  EXMEM_RegWrite=0;EXMEM_MemtoReg=0;EXMEM_Branch=0;EXMEM_MemWrite=0;
  EXMEM_Target=0;
  MEMWB_RegWrite=0;MEMWB_MemtoReg=0;
end
//RUNNING THE PIPELINE
  always @(negedge clock) begin
//STAGE 1 - IF
  PC <= NextPC;
  IFID_PCplus2 <= PCplus2;
  IFID_IR <= IMemory[PC>>1];
//STAGE 2 - ID
  IDEX_IR <= IFID_IR; // For monitoring the pipeline
  // RegDst[1], AluSrc[1], MemtoReg[1], RegWrite[1], MemWrite1[1], BEQ[1], BNE[1], AluCtrl[3]
  {IDEX_RegDst,IDEX_ALUSrc,IDEX_MemtoReg,IDEX_RegWrite,IDEX_MemWrite,IDEX_Branch,IDEX_ALUOp} <= Control;
  IDEX_PCplus2 <= IFID_PCplus2;
  IDEX_RD1 <= RD1;
  IDEX_RD2 <= RD2;
  IDEX_SignExt <= SignExtend;
  IDEX_rt <= IFID_IR[9:8];
  IDEX_rd <= IFID_IR[7:6];
//STAGE 3 - EX
  EXMEM_IR <= IDEX_IR; // For monitoring the pipeline
  EXMEM_RegWrite <= IDEX_RegWrite;
  EXMEM_MemtoReg <= IDEX_MemtoReg;
  EXMEM_Branch <= IDEX_Branch;
  EXMEM_MemWrite <= IDEX_MemWrite;
  EXMEM_Target <= Target;
  EXMEM_Zero <= Zero;
  EXMEM_ALUOut <= ALUOut;
  EXMEM_RD2 <= IDEX_RD2;
  EXMEM_rd <= WR;
//STAGE 4 - MEM
  MEMWB_IR <= EXMEM_IR; // For monitoring the pipeline
  MEMWB_RegWrite <= EXMEM_RegWrite;
  MEMWB_MemtoReg <= EXMEM_MemtoReg;
  MEMWB_MemOut <= MemOut;
  MEMWB_ALUOut <= EXMEM_ALUOut;
  MEMWB_rd <= EXMEM_rd;
//STAGE 5 - WB
// Register write happens on neg edge of the clock (if MEMWB_RegWrite is asserted)
end
endmodule
//********** END OF CPU MODULE **********
//********** TEST MODULE **********
module test ();
  reg clock;
  wire [15:0] PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD;
  CPU test_cpu(clock,PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
  always #1 clock = ~clock;
  initial begin
    $display ("time PC  IFID_IR  IDEX_IR  EXMEM_IR  MEMWB_IR  WD");
    $monitor ("%2d %3d %b %b %b %b %d", $time,PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
    clock = 1;
    #56 $finish; //this number will have to be changed for the # of new instructions
  end
endmodule
