// SPDX-License-Identifier: PMPL-1.0-or-later
// Sample ReScript types for interop testing

// Simple record type
type user = {
  id: int,
  name: string,
  email: string,
  verified: bool,
}

// Record with optional fields
type profile = {
  userId: int,
  bio: option<string>,
  avatar: option<string>,
  tags: array<string>,
}

// Variant type (enum)
type userStatus =
  | Active
  | Inactive
  | Suspended
  | Deleted

// Variant with payload
type result<'a, 'e> =
  | Ok('a)
  | Error('e)

// Nested record
type address = {
  street: string,
  city: string,
  zipCode: string,
  country: string,
}

type person = {
  name: string,
  age: int,
  address: address,
}

// JS interop with @as attribute
type apiUser = {
  @as("user_id") id: int,
  @as("user_name") name: string,
  @as("email_address") email: string,
}

// Tuple type
type coordinates = (float, float, float)

// Map type (Js.Dict.t)
type config = {
  name: string,
  settings: Js.Dict.t<string>,
}

// Polymorphic type
type response<'data> = {
  status: int,
  message: string,
  data: option<'data>,
}

// Type alias
type userId = int
type timestamp = float

// Complex nested structure
type post = {
  id: int,
  authorId: userId,
  title: string,
  content: string,
  tags: array<string>,
  metadata: Js.Dict.t<string>,
  createdAt: timestamp,
  status: userStatus,
}
