;; SPDX-License-Identifier: PMPL-1.0
;; ECOSYSTEM.scm - Ecosystem Positioning
;; protocol-squisher
;;
;; IMPORTANT: Satellite relationships must be kept up to date.
;; When adding/removing satellites, update this file and the satellite's ECOSYSTEM.scm.

(ecosystem
  (version . "1.0.0")
  (name . "protocol-squisher")
  (type . "component")
  (purpose . "")

  (position-in-ecosystem
   (category . "")
   (layer . ""))

  (related-projects . ())

  (what-this-is . ())

  (what-this-is-not . ())

  ;; Maintenance note: Review satellite relationships when:
  ;; - Adding new repos with similar suffix patterns (-ssg, -mcp, -scm, -ffi)
  ;; - Removing or archiving repos
  ;; - Changing the portfolio structure
  (maintenance-checks
   (satellite-sync . "Ensure parent and satellite ECOSYSTEM.scm files are consistent")
   (portfolio-review . "Verify all satellites are listed in parent repo")))
