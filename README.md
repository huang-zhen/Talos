# Talos

Introduction

    Talos automatically instruments Security Workaround for Rapid Response (SWRR) into applications to mitigate software vulnerabilities, at the cost of losing functionality related with the vulnerable code. SWRRs prevent the execution of vulnerable code and steer the execution to existing error handling code to avoid obtrusiveness, i.e. losing functionality unrelated to vulnerabilities.

	SWRRs are oblivious to the nature of vulnerabilities so they can be applied to any vulnerabilities in theory. They are designed to be very simple and easy to be automatically synthesized. As a result, SWRRs can be generated rapidly with minimal information about vulnerabilities.

	Talos supports two deployment modes for SWRRs: in-place and patch-based. In the in-place mode, Talos synthesizes in-place SWRRs and instruments them into every parts of an application that can be protected, before the application is released. In-place deployment allows fast protection without any delay in issuing patches. When a new vulnerability is discovered, the users simply need to activate the SWRR corresponding to the vulnerability to mitigate the vulnerability, without the need to install any new code.

	In the second deployment mode, Talos synthesizes an SWRR targeting a particular vulnerability and the SWRR needs to be installed to make effect for users, similar to a patch. Because an SWRR can be automatically generated rapidly, it can be released in a tiny fraction of the time that required for a regular full patch.

Publication

    "Talos: Neutralizing Vulnerabilities with Security Workarounds for Rapid Response", 
    in the proceedings of the 37th IEEE Symposium on Security and Privacy (Oakland 2016). 
