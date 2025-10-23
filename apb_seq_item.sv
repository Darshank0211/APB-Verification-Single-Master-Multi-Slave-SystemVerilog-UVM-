//creating own datatype for specific operations
typedef enum {write,read,wr_rd} op_t;
class apb_seq_item extends uvm_sequence_item;

//randomizing the input

rand op_t op;

     bit       pclk ;
     bit       presetn;
rand bit [31:0]paddr  ;
     bit       penable;
rand bit       psel   ;
     bit       pready ;
rand bit       pwrite ;
rand bit [31:0]pwdata ;
     bit [31:0]prdata ;
     bit       pslverr;

`uvm_object_utils_begin(apb_seq_item)

`uvm_field_enum(op_t,op,UVM_ALL_ON);

`uvm_field_int(pclk     ,UVM_ALL_ON); 	         
`uvm_field_int(presetn  ,UVM_ALL_ON);
`uvm_field_int(paddr    ,UVM_ALL_ON);
`uvm_field_int(penable  ,UVM_ALL_ON);
`uvm_field_int(psel     ,UVM_ALL_ON);
`uvm_field_int(pready   ,UVM_ALL_ON);
`uvm_field_int(pwrite   ,UVM_ALL_ON);
`uvm_field_int(pwdata   ,UVM_ALL_ON);
`uvm_field_int(prdata   ,UVM_ALL_ON);
`uvm_field_int(pslverr  ,UVM_ALL_ON);

`uvm_object_utils_end


function new(string name ="apb_seq_item");
	super.new(name);
endfunction

//creating constrains for the randomizations

constraint paddr_c {
  paddr inside {
    [32'h00000001:32'h000000FF],   // Slave 0
    [32'h00000100:32'h000001FF],   // Slave 1
    [32'h00000200:32'h000002FF],   // Slave 2
    [32'h00000300:32'h000003FF]    // Slave 3
  };
}

constraint psel_c { psel inside{1,0};
	            (paddr inside{[32'h00000001:32'h000000FF]})->(psel==1);
		    (paddr inside{[32'h00000100:32'h000001FF]})->(psel==1);
		    (paddr inside{[32'h00000200:32'h000002FF]})->(psel==1);
		    (paddr inside{[32'h00000300:32'h000003FF]})->(psel==1);
		      
		    }

constraint pwrite_c {
        if (op == write) 
            pwrite == 1'b1;
        else if (op == read)
            pwrite == 1'b0;
    }

//constraint pwdata_c { pwdata inside {[32'h00000001:32'h000000FF]};}

constraint op_t_c { (op==write)->(pwrite==1);
		    (op==read)->(pwrite==0);
		  }

constraint pwdata_c {
  pwdata inside {
    32'h00000001,
    [32'h00000002:32'h000000FF],
    [32'h00000100:32'h0000FFFF]
  };
}
endclass
