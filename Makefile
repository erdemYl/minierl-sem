.PHONY: build test check all 

REBAR = rebar3

build:
	$(REBAR) compile

clean:
	$(REBAR) clean

check:
	$(REBAR) dialyzer
	$(REBAR) eunit 
	$(REBAR) proper -n 1000


all: build check 

