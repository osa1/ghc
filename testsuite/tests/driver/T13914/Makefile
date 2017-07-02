TOP=../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

t13914:
	echo "Without -fignore-asserts"
	'$(TEST_HC)' $(TEST_HC_OPTS) main.hs
	(./main 2>&1); true
	echo "With -fignore-asserts"
	'$(TEST_HC)' $(TEST_HC_OPTS) -fignore-asserts main.hs
	./main 2>&1
	echo "Without -fignore-asserts"
	'$(TEST_HC)' $(TEST_HC_OPTS) main.hs
	(./main 2>&1); true
