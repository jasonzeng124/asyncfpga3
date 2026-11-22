module {
  func.func @matrix(%arg0: memref<900xi32> {handshake.arg_name = "inA"}, %arg1: memref<900xi32> {handshake.arg_name = "inB"}, %arg2: memref<900xi32> {handshake.arg_name = "outC"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb4
    %c0_i32_1 = arith.constant {handshake.name = "constant9"} 0 : i32
    %4 = arith.extui %3 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb3(%c0_i32_1, %c0_i32_1 : i32, i32) {handshake.name = "br2"}
  ^bb3(%5: i32, %6: i32):  // 2 preds: ^bb2, ^bb3
    %c30_i32 = arith.constant {handshake.name = "constant10"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant11"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant12"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant13"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant14"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant15"} 1 : i64
    %7 = arith.extui %5 {handshake.name = "extui3"} : i32 to i64
    %8 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %9 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %10 = arith.addi %8, %9 {handshake.name = "addi7"} : i64
    %11 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %12 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %13 = arith.addi %11, %12 {handshake.name = "addi8"} : i64
    %14 = arith.addi %10, %13 {handshake.name = "addi9"} : i64
    %15 = arith.addi %14, %7 {handshake.name = "addi0"} : i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast0"} : i64 to index
    %17 = memref.load %arg0[%16] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<900xi32>
    %18 = arith.extui %5 {handshake.name = "extui4"} : i32 to i64
    %19 = arith.shli %18, %c1_i64 {handshake.name = "shli4"} : i64
    %20 = arith.shli %18, %c2_i64 {handshake.name = "shli5"} : i64
    %21 = arith.addi %19, %20 {handshake.name = "addi10"} : i64
    %22 = arith.shli %18, %c3_i64 {handshake.name = "shli6"} : i64
    %23 = arith.shli %18, %c4_i64 {handshake.name = "shli7"} : i64
    %24 = arith.addi %22, %23 {handshake.name = "addi11"} : i64
    %25 = arith.addi %21, %24 {handshake.name = "addi12"} : i64
    %26 = arith.addi %25, %4 {handshake.name = "addi1"} : i64
    %27 = arith.index_cast %26 {handshake.name = "index_cast1"} : i64 to index
    %28 = memref.load %arg1[%27] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<900xi32>
    %29 = arith.muli %17, %28 {handshake.name = "muli2"} : i32
    %30 = arith.addi %6, %29 {handshake.name = "addi2"} : i32
    %31 = arith.addi %5, %c1_i32 {handshake.name = "addi3"} : i32
    %32 = arith.cmpi ult, %31, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %32, ^bb3(%31, %30 : i32, i32), ^bb4(%30 : i32) {handshake.name = "cond_br0"}
  ^bb4(%33: i32):  // pred: ^bb3
    %c30_i32_2 = arith.constant {handshake.name = "constant16"} 30 : i32
    %c1_i32_3 = arith.constant {handshake.name = "constant17"} 1 : i32
    %c4_i64_4 = arith.constant {handshake.name = "constant18"} 4 : i64
    %c3_i64_5 = arith.constant {handshake.name = "constant19"} 3 : i64
    %c2_i64_6 = arith.constant {handshake.name = "constant20"} 2 : i64
    %c1_i64_7 = arith.constant {handshake.name = "constant21"} 1 : i64
    %34 = arith.extui %3 {handshake.name = "extui5"} : i32 to i64
    %35 = arith.shli %2, %c1_i64_7 {handshake.name = "shli8"} : i64
    %36 = arith.shli %2, %c2_i64_6 {handshake.name = "shli9"} : i64
    %37 = arith.addi %35, %36 {handshake.name = "addi13"} : i64
    %38 = arith.shli %2, %c3_i64_5 {handshake.name = "shli10"} : i64
    %39 = arith.shli %2, %c4_i64_4 {handshake.name = "shli11"} : i64
    %40 = arith.addi %38, %39 {handshake.name = "addi14"} : i64
    %41 = arith.addi %37, %40 {handshake.name = "addi15"} : i64
    %42 = arith.addi %41, %34 {handshake.name = "addi4"} : i64
    %43 = arith.index_cast %42 {handshake.name = "index_cast2"} : i64 to index
    memref.store %33, %arg2[%43] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : memref<900xi32>
    %44 = arith.addi %3, %c1_i32_3 {handshake.name = "addi5"} : i32
    %45 = arith.cmpi ult, %44, %c30_i32_2 {handshake.name = "cmpi1"} : i32
    cf.cond_br %45, ^bb2(%44 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c30_i32_8 = arith.constant {handshake.name = "constant22"} 30 : i32
    %c1_i32_9 = arith.constant {handshake.name = "constant23"} 1 : i32
    %46 = arith.addi %0, %c1_i32_9 {handshake.name = "addi6"} : i32
    %47 = arith.cmpi ult, %46, %c30_i32_8 {handshake.name = "cmpi2"} : i32
    cf.cond_br %47, ^bb1(%46 : i32), ^bb6 {handshake.name = "cond_br2"}
  ^bb6:  // pred: ^bb5
    return {handshake.name = "return0"}
  }
}

