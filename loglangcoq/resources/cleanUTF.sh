#!/bin/bash

##code uft8 from http://fr.wikipedia.org/wiki/Exposants_et_indices_Unicode

C1=$(python -c 'print u"\u00B2".encode("utf8")')
#echo $C1
C2=$(python -c 'print u"\u00B3".encode("utf8")')
#echo $C2
C3=$(python -c 'print u"\u00B9".encode("utf8")')
#echo $C3
C4=$(python -c 'print u"\u2070".encode("utf8")')
#echo $C4
C5=$(python -c 'print u"\u2071".encode("utf8")')
#echo $C5
C6=$(python -c 'print u"\u2074".encode("utf8")')
#echo $C6
C7=$(python -c 'print u"\u2075".encode("utf8")')
#echo $C7
C8=$(python -c 'print u"\u2076".encode("utf8")')
#echo $C8
C9=$(python -c 'print u"\u2077".encode("utf8")')
#echo $C9
C10=$(python -c 'print u"\u2078".encode("utf8")')
#echo $C10
C11=$(python -c 'print u"\u2079".encode("utf8")')
#echo $C11
C12=$(python -c 'print u"\u207A".encode("utf8")')
#echo $C12
C13=$(python -c 'print u"\u207B".encode("utf8")')
#echo $C13
C14=$(python -c 'print u"\u207C".encode("utf8")')
#echo $C14
C15=$(python -c 'print u"\u209D".encode("utf8")')
#echo $C15
C16=$(python -c 'print u"\u209E".encode("utf8")')
#echo $C16
C17=$(python -c 'print u"\u209F".encode("utf8")')
#echo $C17


sed -i -s 's/['"$C1"']/<sup>2<\/sup>/g ;s/['"$C2"']/<sup>3<\/sup>/g ; s/['"$C3"']/<sup>1<\/sup>/g' $1

sed -i -s 's/['"$C4"']/<sup>0<\/sup>/g ;s/['"$C5"']/<sup>i<\/sup>/g ; s/['"$C6"']/<sup>4<\/sup>/g' $1


sed -i -s 's/['"$C7"']/<sup>5<\/sup>/g ;s/['"$C8"']/<sup>6<\/sup>/g ; s/['"$C9"']/<sup>7<\/sup>/g' $1


sed -i -s 's/['"$C10"']/<sup>8<\/sup>/g ;s/['"$C11"']/<sup>9<\/sup>/g ; s/['"$C12"']/<sup>+<\/sup>/g' $1


sed -i -s 's/['"$C13"']/<sup>-<\/sup>/g ;s/['"$C14"']/<sup>=<\/sup>/g ; s/['"$C15"']/<sup>(<\/sup>/g' $1


sed -i -s 's/['"$C16"']/<sup>)<\/sup>/g ;s/['"$C17"']/<sup>n<\/sup>/g' $1

C18=$(python -c 'print u"\u2080".encode("utf8")')
#echo $C18

C19=$(python -c 'print u"\u2081".encode("utf8")')
#echo $C19

C20=$(python -c 'print u"\u2082".encode("utf8")')
#echo $C20

C21=$(python -c 'print u"\u2083".encode("utf8")')
#echo $C21

C22=$(python -c 'print u"\u2084".encode("utf8")')
#echo $C21

C23=$(python -c 'print u"\u2085".encode("utf8")')
#echo $C23

C24=$(python -c 'print u"\u2086".encode("utf8")')
#echo $C24

C25=$(python -c 'print u"\u2087".encode("utf8")')
#echo $C25

C26=$(python -c 'print u"\u2088".encode("utf8")')
#echo $C26

C27=$(python -c 'print u"\u2089".encode("utf8")')
#echo $C17

C28=$(python -c 'print u"\u208A".encode("utf8")')
#echo $C28

C29=$(python -c 'print u"\u208B".encode("utf8")')
#echo $C29

C30=$(python -c 'print u"\u208C".encode("utf8")')
#echo $C30

C31=$(python -c 'print u"\u208D".encode("utf8")')
#echo $C31

C32=$(python -c 'print u"\u208E".encode("utf8")')

#echo $C33

C33=$(python -c 'print u"\u2090".encode("utf8")')
#echo $C23

C34=$(python -c 'print u"\u2091".encode("utf8")')
#echo $C34

C35=$(python -c 'print u"\u2092".encode("utf8")')
#echo $C35

C36=$(python -c 'print u"\u2093".encode("utf8")')
#echo $C36

C37=$(python -c 'print u"\u2094".encode("utf8")')
#echo $C37

C38=$(python -c 'print u"\u2095".encode("utf8")')
#echo $C38

C39=$(python -c 'print u"\u2096".encode("utf8")')
#echo $C39

C40=$(python -c 'print u"\u2097".encode("utf8")')
#echo $C40

C41=$(python -c 'print u"\u2098".encode("utf8")')
#echo $C41

C42=$(python -c 'print u"\u2099".encode("utf8")')
#echo $C42

C43=$(python -c 'print u"\u209A".encode("utf8")')
#echo $C43

C44=$(python -c 'print u"\u209B".encode("utf8")')
#echo $C44

C45=$(python -c 'print u"\u209C".encode("utf8")')
#echo $C45



sed -i -s 's/['"$C18"']/<sub>0<\/sub>/g ;s/['"$C19"']/<sub>1<\/sub>/g ; s/['"$C20"']/<sub>2<\/sub>/g' $1

sed -i -s 's/['"$C21"']/<sub>3<\/sub>/g ;s/['"$C22"']/<sub>4<\/sub>/g ; s/['"$C23"']/<sub>5<\/sub>/g' $1

sed -i -s 's/['"$C24"']/<sub>6<\/sub>/g ;s/['"$C25"']/<sub>7<\/sub>/g ; s/['"$C26"']/<sub>8<\/sub>/g' $1

sed -i -s 's/['"$C27"']/<sub>9<\/sub>/g ;s/['"$C28"']/<sub>+<\/sub>/g ; s/['"$C29"']/<sub>-<\/sub>/g' $1

sed -i -s 's/['"$C30"']/<sub>=<\/sub>/g ;s/['"$C31"']/<sub>(<\/sub>/g ; s/['"$C32"']/<sub>)<\/sub>/g' $1



sed -i -s 's/['"$C33"']/<sub>a<\/sub>/g ;s/['"$C34"']/<sub>e<\/sub>/g ; s/['"$C35"']/<sub>o<\/sub>/g' $1


sed -i -s 's/['"$C36"']/<sub>x<\/sub>/g ;s/['"$C37"']/<sub>ə<\/sub>/g ; s/['"$C38"']/<sub>h<\/sub>/g' $1

sed -i -s 's/['"$C39"']/<sub>k<\/sub>/g ;s/['"$C40"']/<sub>l<\/sub>/g ; s/['"$C41"']/<sub>m<\/sub>/g' $1

sed -i -s 's/['"$C42"']/<sub>n<\/sub>/g ;s/['"$C43"']/<sub>p<\/sub>/g ; s/['"$C44"']/<sub>s<\/sub>/g' $1

sed -i -s 's/['"$C45"']/<sub>t<\/sub>/g' $1


#echo "seconde vague"
#echo $C1
#echo $C2
#echo $C3
#echo $C4
#echo $C5
#echo $C6
#echo $C7
#echo $C8
#echo $C9
#echo $C10
#echo $C11
#echo $C12
#echo $C13
#echo $C14
#echo $C15
#echo $C16
#echo $C17
#echo $C18
#echo $C19
#echo $C20
#echo $C21
#echo $C21
#echo $C23
#echo $C24
#echo $C25
#echo $C26
#echo $C17
#echo $C28
#echo $C29
#echo $C30
#echo $C31
#echo $C33
#echo $C23
#echo $C34
#echo $C35
#echo $C36
#echo $C37
#echo $C38
#echo $C39
#echo $C40
#echo $C41
#echo $C42
#echo $C43
#echo $C44
#echo $C45
echo "Clean UTF8 ->HTML ==================================== DONE ==";
