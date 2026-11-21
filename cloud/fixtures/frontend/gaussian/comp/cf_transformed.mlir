module {
  func.func @gaussian(%arg0: memref<20xi32> {handshake.arg_name = "c"}, %arg1: memref<400xi32> {handshake.arg_name = "a"}) -> i32 {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    cf.br ^bb1(%c1_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c19_i32 = arith.constant {handshake.name = "constant7"} 19 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant8"} 1 : i32
    %1 = arith.addi %0, %c1_i32_0 {handshake.name = "addi0"} : i32
    %2 = arith.cmpi ult, %1, %c19_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %2, ^bb3(%1 : i32), ^bb5 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb4
    %c19_i32_1 = arith.constant {handshake.name = "constant9"} 19 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant10"} 1 : i32
    %3 = arith.addi %5, %c1_i32_2 {handshake.name = "addi1"} : i32
    %4 = arith.cmpi ult, %3, %c19_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %4, ^bb3(%3 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb3(%5: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_3 = arith.constant {handshake.name = "constant11"} 1 : i32
    %6 = arith.extui %5 {handshake.name = "extui0"} : i32 to i64
    %7 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %8 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %9 = arith.extui %5 {handshake.name = "extui3"} : i32 to i64
    cf.br ^bb4(%c1_i32_3 : i32) {handshake.name = "br1"}
  ^bb4(%10: i32):  // 2 preds: ^bb3, ^bb4
    %c20_i32 = arith.constant {handshake.name = "constant12"} 20 : i32
    %c1_i32_4 = arith.constant {handshake.name = "constant13"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant14"} 4 : i64
    %c2_i64 = arith.constant {handshake.name = "constant15"} 2 : i64
    %11 = arith.extui %10 {handshake.name = "extui4"} : i32 to i64
    %12 = arith.shli %6, %c2_i64 {handshake.name = "shli0"} : i64
    %13 = arith.shli %6, %c4_i64 {handshake.name = "shli1"} : i64
    %14 = arith.addi %12, %13 {handshake.name = "addi7"} : i64
    %15 = arith.addi %14, %11 {handshake.name = "addi2"} : i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast0"} : i64 to index
    %17 = memref.load %arg1[%16] {handshake.name = "load0"} : memref<400xi32>
    %18 = arith.index_cast %7 {handshake.name = "index_cast1"} : i64 to index
    %19 = memref.load %arg0[%18] {handshake.name = "load1"} : memref<20xi32>
    %20 = arith.extui %10 {handshake.name = "extui5"} : i32 to i64
    %21 = arith.shli %8, %c2_i64 {handshake.name = "shli2"} : i64
    %22 = arith.shli %8, %c4_i64 {handshake.name = "shli3"} : i64
    %23 = arith.addi %21, %22 {handshake.name = "addi8"} : i64
    %24 = arith.addi %23, %20 {handshake.name = "addi3"} : i64
    %25 = arith.index_cast %24 {handshake.name = "index_cast2"} : i64 to index
    %26 = memref.load %arg1[%25] {handshake.name = "load2"} : memref<400xi32>
    %27 = arith.muli %19, %26 {handshake.name = "muli2"} : i32
    %28 = arith.subi %17, %27 {handshake.name = "subi0"} : i32
    %29 = arith.extui %10 {handshake.name = "extui6"} : i32 to i64
    %30 = arith.shli %9, %c2_i64 {handshake.name = "shli4"} : i64
    %31 = arith.shli %9, %c4_i64 {handshake.name = "shli5"} : i64
    %32 = arith.addi %30, %31 {handshake.name = "addi9"} : i64
    %33 = arith.addi %32, %29 {handshake.name = "addi4"} : i64
    %34 = arith.index_cast %33 {handshake.name = "index_cast3"} : i64 to index
    memref.store %28, %arg1[%34] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<400xi32>
    %35 = arith.addi %10, %c1_i32_4 {handshake.name = "addi5"} : i32
    %36 = arith.cmpi ult, %35, %c20_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %36, ^bb4(%35 : i32), ^bb2 {handshake.name = "cond_br2"}
  ^bb5:  // 2 preds: ^bb1, ^bb2
    %c19_i32_5 = arith.constant {handshake.name = "constant16"} 19 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant17"} 1 : i32
    %37 = arith.addi %0, %c1_i32_6 {handshake.name = "addi6"} : i32
    %38 = arith.cmpi ult, %37, %c19_i32_5 {handshake.name = "cmpi3"} : i32
    cf.cond_br %38, ^bb1(%37 : i32), ^bb6 {handshake.name = "cond_br3"}
  ^bb6:  // pred: ^bb5
    %c29070_i32 = arith.constant {handshake.name = "constant18"} 29070 : i32
    return {handshake.name = "return0"} %c29070_i32 : i32
  }
}

