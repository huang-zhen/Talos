#!/bin/bash
echo "Running Talos..."
if [ -z "$TALOS_DIR" ]; then
    echo "Error: TALOS_DIR not set"
    exit
fi
if [ $# -lt 3 ]; then
	echo "Usage: $0 app binary analyzer_output"
	exit
fi
APP=$1
BINARY=$2
ANALYZER_OUTPUT=$3
file $BINARY|grep ELF
if [ $? -eq 0 ]; then
    echo "ELF binary"
    API_ERROR=$TALOS_DIR/API_Specs/Linux_API_error.txt
else
    file $APP|grep PE
    if [ $? -eq 0 ]; then
        echo "Windows binary"
        API_ERROR=$TALOS_DIR/API_Specs/Windows_API_error.txt
    else
        echo "Unknown binary type"
		exit
    fi
fi
ANALYZER_CFG=$TALOS_DIR/analyzer.cfg
if [ ! -e $ANALYZER_CFG ]; then
	echo "$ANALYZER_CFG does not exist!"
	exit
fi
SWRRS=$APP.SWRRs
TALOS=$TALOS_DIR/talos.py
rm -rf $SWRRS
# remove ^M in input file
sed -i -e "s/\r//g" "$ANALYZER_OUTPUT"
$TALOS -a $API_ERROR -d -F $ANALYZER_CFG -S $APP.talos_log -K -E main $ANALYZER_OUTPUT 2>$APP.talos_err
if [ $? -ne 0 ]; then
    echo "Error running $TALOS, please check $APP.talos_err"
    exit
fi
