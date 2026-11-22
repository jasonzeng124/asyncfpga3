module {
  func.func @matrix_power(%arg0: memref<400xi32> {handshake.arg_name = "mat"}, %arg1: memref<20xi32> {handshake.arg_name = "row"}, %arg2: memref<20xi32> {handshake.arg_name = "col"}, %arg3: memref<20xi32> {handshake.arg_name = "a"}) {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    cf.br ^bb1(%c1_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32 = arith.constant {handshake.name = "constant7"} 0 : i32
    %c-1_i32 = arith.constant {handshake.name = "constant8"} -1 : i32
    %1 = arith.addi %0, %c-1_i32 {handshake.name = "addi0"} : i32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%c0_i32 : i32) {handshake.name = "br1"}
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb2
    %c20_i32 = arith.constant {handshake.name = "constant9"} 20 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant11"} 4 : i64
    %c2_i64 = arith.constant {handshake.name = "constant12"} 2 : i64
    %5 = arith.extui %4 {handshake.name = "extui2"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast0"} : i64 to index
    %7 = memref.load %arg3[%6] {handshake.name = "load0"} : memref<20xi32>
    %8 = arith.extui %4 {handshake.name = "extui3"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast1"} : i64 to index
    %10 = memref.load %arg2[%9] {handshake.name = "load1"} : memref<20xi32>
    %11 = arith.extsi %10 {handshake.name = "extsi0"} : i32 to i64
    %12 = arith.shli %2, %c2_i64 {handshake.name = "shli0"} : i64
    %13 = arith.shli %2, %c4_i64 {handshake.name = "shli1"} : i64
    %14 = arith.addi %12, %13 {handshake.name = "addi6"} : i64
    %15 = arith.addi %14, %11 {handshake.name = "addi1"} : i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast2"} : i64 to index
    %17 = memref.load %arg0[%16] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : memref<400xi32>
    %18 = arith.muli %7, %17 {handshake.name = "muli1"} : i32
    %19 = arith.extui %4 {handshake.name = "extui4"} : i32 to i64
    %20 = arith.index_cast %19 {handshake.name = "index_cast3"} : i64 to index
    %21 = memref.load %arg1[%20] {handshake.name = "load3"} : memref<20xi32>
    %22 = arith.extsi %21 {handshake.name = "extsi1"} : i32 to i64
    %23 = arith.shli %3, %c2_i64 {handshake.name = "shli2"} : i64
    %24 = arith.shli %3, %c4_i64 {handshake.name = "shli3"} : i64
    %25 = arith.addi %23, %24 {handshake.name = "addi7"} : i64
    %26 = arith.addi %25, %22 {handshake.name = "addi2"} : i64
    %27 = arith.index_cast %26 {handshake.name = "index_cast4"} : i64 to index
    %28 = memref.load %arg0[%27] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load4"} : memref<400xi32>
    %29 = arith.addi %28, %18 {handshake.name = "addi3"} : i32
    %30 = arith.index_cast %26 {handshake.name = "index_cast5"} : i64 to index
    memref.store %29, %arg0[%30] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<400xi32>
    %31 = arith.addi %4, %c1_i32_0 {handshake.name = "addi4"} : i32
    %32 = arith.cmpi ult, %31, %c20_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %32, ^bb2(%31 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c20_i32_1 = arith.constant {handshake.name = "constant13"} 20 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant14"} 1 : i32
    %33 = arith.addi %0, %c1_i32_2 {handshake.name = "addi5"} : i32
    %34 = arith.cmpi ult, %33, %c20_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %34, ^bb1(%33 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

