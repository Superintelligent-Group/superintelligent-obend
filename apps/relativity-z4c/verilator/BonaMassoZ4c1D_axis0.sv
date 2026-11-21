module BonaMassoZ4c1D_flux_axis0 (
  input  logic        clk,
  input  logic        rst,
  input  logic [63:0] alpha,
  input  logic [63:0] gxx,
  input  logic [63:0] Ax,
  input  logic [63:0] Dx,
  input  logic [63:0] Kxx,
  input  logic [63:0] Theta,
  output logic [63:0] flux_out_0,
  output logic [63:0] flux_out_1,
  output logic [63:0] flux_out_2,
  output logic [63:0] flux_out_3,
  output logic [63:0] flux_out_4,
  output logic [63:0] flux_out_5
);
  logic [63:0] w_0; // ssa_w0
  logic [63:0] w_1; // ssa_w1
  logic [63:0] w_2; // ssa_w2
  logic [63:0] w_3; // ssa_w3
  logic [63:0] w_4; // ssa_w4
  logic [63:0] w_5; // ssa_w5
  logic [63:0] w_6; // ssa_w6
  logic [63:0] w_7; // ssa_w7
  logic [63:0] w_8; // ssa_w8
  logic [63:0] w_9; // ssa_w9
  logic [63:0] w_10; // ssa_w10
  logic [63:0] w_11; // ssa_w11
  logic [63:0] w_12; // ssa_w12
  logic [63:0] w_13; // ssa_w13
  logic [63:0] w_14; // ssa_w14
  logic [63:0] w_15; // ssa_w15
  logic [63:0] w_16; // ssa_w16
  logic [63:0] w_17; // ssa_w17
  logic [63:0] w_18; // ssa_w18
  logic [63:0] w_19; // ssa_w19
  logic [63:0] w_20; // ssa_w20
  logic [63:0] w_21; // ssa_w21
  logic [63:0] w_22; // ssa_w22
  logic [63:0] w_23; // ssa_w23
  logic [63:0] w_24; // ssa_w24
  logic [63:0] w_25; // ssa_w25
  logic [63:0] w_26; // ssa_w26
  logic [63:0] w_27; // ssa_w27
  logic [63:0] w_28; // ssa_w28
  logic [63:0] w_29; // ssa_w29
  logic [63:0] w_30; // ssa_w30
  logic [63:0] w_31; // ssa_w31
  logic [63:0] w_32; // ssa_w32
  logic [63:0] w_33; // ssa_w33
  logic [63:0] w_34; // ssa_w34
  logic [63:0] w_35; // ssa_w35
  logic [63:0] w_36; // ssa_w36
  logic [63:0] w_37; // ssa_w37
  logic [63:0] w_38; // ssa_w38
  logic [63:0] w_39; // ssa_w39
  logic [63:0] w_40; // ssa_w40
  logic [63:0] w_41; // ssa_w41
  logic [63:0] w_42; // ssa_w42
  logic [63:0] w_43; // ssa_w43
  logic [63:0] w_44; // ssa_w44
  logic [63:0] w_45; // ssa_w45
  logic [63:0] w_46; // ssa_w46
  logic [63:0] w_47; // ssa_w47
  logic [63:0] w_48; // ssa_w48
  logic [63:0] w_49; // ssa_w49
  logic [63:0] w_50; // ssa_w50
  logic [63:0] w_51; // ssa_w51
  logic [63:0] w_52; // ssa_w52
  logic [63:0] w_53; // ssa_w53
  logic [63:0] w_54; // ssa_w54
  logic [63:0] w_55; // ssa_w55
  logic [63:0] w_56; // ssa_w56
  logic [63:0] w_57; // ssa_w57
  logic [63:0] w_58; // ssa_w58
  logic [63:0] flux_pipe_r0;
  logic [63:0] flux_pipe_r1;
  logic [63:0] flux_pipe_r2;
  logic [63:0] flux_pipe_r3;
  logic [63:0] flux_pipe_r4;
  logic [63:0] flux_pipe_r5;
  always_comb begin
    w_0 = 64'd858993459;
    w_1 = alpha;
    w_2 = 64'((128'($signed(64'(w_0))) * 128'($signed(64'(w_1)))) >>> 32);
    w_3 = (64'd0 - w_2);
    w_4 = gxx;
    w_5 = 64'((128'($signed(64'(w_0))) * 128'($signed(64'(w_4)))) >>> 32);
    w_6 = (64'd0 - w_5);
    w_7 = Ax;
    w_8 = 64'((128'($signed(64'(w_0))) * 128'($signed(64'(w_7)))) >>> 32);
    w_9 = (64'd0 - w_8);
    w_10 = 64'd8589934592;
    w_11 = Kxx;
    w_12 = ($signed(w_4) < $signed(64'd0) ? 64'd1 : 64'd0);
    w_13 = ((w_12 != 64'd0) ? (64'd0 - w_4) : w_4);
    w_14 = 64'd0;
    w_15 = (w_13 < 64'd2147483648 ? 64'd1 : 64'd0);
    w_16 = ((w_15 != 64'd0) ? (w_13 << (64'd32 & 64'd63)) : w_13);
    w_17 = ((w_15 != 64'd0) ? (w_14 + 64'd32) : w_14);
    w_18 = (w_16 < 64'd140737488355328 ? 64'd1 : 64'd0);
    w_19 = ((w_18 != 64'd0) ? (w_16 << (64'd16 & 64'd63)) : w_16);
    w_20 = ((w_18 != 64'd0) ? (w_17 + 64'd16) : w_17);
    w_21 = (w_19 < 64'd36028797018963968 ? 64'd1 : 64'd0);
    w_22 = ((w_21 != 64'd0) ? (w_19 << (64'd8 & 64'd63)) : w_19);
    w_23 = ((w_21 != 64'd0) ? (w_20 + 64'd8) : w_20);
    w_24 = (w_22 < 64'd576460752303423488 ? 64'd1 : 64'd0);
    w_25 = ((w_24 != 64'd0) ? (w_22 << (64'd4 & 64'd63)) : w_22);
    w_26 = ((w_24 != 64'd0) ? (w_23 + 64'd4) : w_23);
    w_27 = (w_25 < 64'd2305843009213693952 ? 64'd1 : 64'd0);
    w_28 = ((w_27 != 64'd0) ? (w_25 << (64'd2 & 64'd63)) : w_25);
    w_29 = ((w_27 != 64'd0) ? (w_26 + 64'd2) : w_26);
    w_30 = (w_28 < 64'd4611686018427387904 ? 64'd1 : 64'd0);
    w_31 = ((w_30 != 64'd0) ? (w_28 << (64'd1 & 64'd63)) : w_28);
    w_32 = ((w_30 != 64'd0) ? (w_29 + 64'd1) : w_29);
    w_33 = ((w_31 + 64'd1073741824) >> (64'd31 & 64'd63));
    w_34 = (64'd12126966482 - 64'((128'($signed(64'(64'd8084644321))) * 128'($signed(64'(w_33)))) >>> 32));
    w_35 = 64'((128'($signed(64'(w_34))) * 128'($signed(64'((64'd8589934592 - 64'((128'($signed(64'(w_33))) * 128'($signed(64'(w_34)))) >>> 32)))))) >>> 32);
    w_36 = 64'((128'($signed(64'(w_35))) * 128'($signed(64'((64'd8589934592 - 64'((128'($signed(64'(w_33))) * 128'($signed(64'(w_35)))) >>> 32)))))) >>> 32);
    w_37 = 64'((128'($signed(64'(w_36))) * 128'($signed(64'((64'd8589934592 - 64'((128'($signed(64'(w_33))) * 128'($signed(64'(w_36)))) >>> 32)))))) >>> 32);
    w_38 = 64'((128'($signed(64'(w_37))) * 128'($signed(64'((64'd8589934592 - 64'((128'($signed(64'(w_33))) * 128'($signed(64'(w_37)))) >>> 32)))))) >>> 32);
    w_39 = (((w_32 < 64'd31 ? 64'd1 : 64'd0) != 64'd0) ? (w_38 >> ((64'd31 - w_32) & 64'd63)) : (w_38 << ((w_32 - 64'd31) & 64'd63)));
    w_40 = ((w_12 != 64'd0) ? (64'd0 - w_39) : w_39);
    w_41 = 64'((128'($signed(64'(w_11))) * 128'($signed(64'(w_40)))) >>> 32);
    w_42 = Theta;
    w_43 = 64'((128'($signed(64'(w_10))) * 128'($signed(64'(w_42)))) >>> 32);
    w_44 = (w_41 - w_43);
    w_45 = 64'((128'($signed(64'(w_1))) * 128'($signed(64'(w_44)))) >>> 32);
    w_46 = 64'((128'($signed(64'(w_10))) * 128'($signed(64'(w_45)))) >>> 32);
    w_47 = (w_9 + w_46);
    w_48 = Dx;
    w_49 = 64'((128'($signed(64'(w_0))) * 128'($signed(64'(w_48)))) >>> 32);
    w_50 = (64'd0 - w_49);
    w_51 = 64'((128'($signed(64'(w_1))) * 128'($signed(64'(w_41)))) >>> 32);
    w_52 = (w_50 + w_51);
    w_53 = 64'((128'($signed(64'(w_0))) * 128'($signed(64'(w_11)))) >>> 32);
    w_54 = (64'd0 - w_53);
    w_55 = 64'((128'($signed(64'(w_1))) * 128'($signed(64'(w_7)))) >>> 32);
    w_56 = (w_54 + w_55);
    w_57 = 64'((128'($signed(64'(w_0))) * 128'($signed(64'(w_42)))) >>> 32);
    w_58 = (64'd0 - w_57);
    flux_out_0 = flux_pipe_r0;
    flux_out_1 = flux_pipe_r1;
    flux_out_2 = flux_pipe_r2;
    flux_out_3 = flux_pipe_r3;
    flux_out_4 = flux_pipe_r4;
    flux_out_5 = flux_pipe_r5;
  end
  // Synchronous-reset control registers
  always_ff @(posedge clk) begin
    if (rst) begin
      flux_pipe_r0 <= 64'd0;
      flux_pipe_r1 <= 64'd0;
      flux_pipe_r2 <= 64'd0;
      flux_pipe_r3 <= 64'd0;
      flux_pipe_r4 <= 64'd0;
      flux_pipe_r5 <= 64'd0;
    end else begin
      flux_pipe_r0 <= w_3;
      flux_pipe_r1 <= w_6;
      flux_pipe_r2 <= w_47;
      flux_pipe_r3 <= w_52;
      flux_pipe_r4 <= w_56;
      flux_pipe_r5 <= w_58;
    end
  end
endmodule
