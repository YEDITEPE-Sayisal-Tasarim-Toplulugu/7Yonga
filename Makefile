


dependences:
	# core repo:
	- make -C gateware/core/ setup

	# axi repo:
	- make -C gateware/axi4 setup

	# axi repo:
	- make -C gateware/pulp_common_cell setup