#!/bin/bash
TALOS_DIR=/data/public/Talos
echo "Running Talos..."
if [ -z "$TALOS_DIR" ]; then
    echo "TALOS_DIR envirnoment variable is not set"
    exit
fi
if [ $# -lt 2 ]; then
	echo "Usage: $0 app analyzer_output"
	exit
fi
APP=$1
ANALYZER_OUTPUT=$2
file $APP|grep ELF
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
