PROBCLI=probcli
portscan_v3:
	$(PROBCLI) PortScanAttackASTD_v3.P -- 30 data/port_scan_exploit.log
library:
	$(PROBCLI) LibraryASTD.P --model-check