extern "C" {
	fn tinysnark_init_public_params();
	fn tinysnark_test();
}

pub fn test() {
	unsafe { tinysnark_init_public_params(); }
	unsafe { tinysnark_test(); }
}