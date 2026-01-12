# Real-world schema: GitHub API types (Pydantic v2)
from pydantic import BaseModel, Field
from typing import Optional, List
from enum import Enum


class UserType(str, Enum):
    user = "User"
    organization = "Organization"
    bot = "Bot"


class User(BaseModel):
    id: int
    login: str
    avatar_url: str
    type: UserType = Field(alias="type")
    site_admin: bool


class Label(BaseModel):
    id: int
    name: str
    color: str
    description: Optional[str] = None


class MilestoneState(str, Enum):
    open = "open"
    closed = "closed"


class Milestone(BaseModel):
    id: int
    number: int
    title: str
    description: Optional[str] = None
    state: MilestoneState
    open_issues: int
    closed_issues: int
    due_on: Optional[str] = None


class IssueState(str, Enum):
    open = "open"
    closed = "closed"


class Issue(BaseModel):
    id: int
    number: int
    title: str
    body: Optional[str] = None
    state: IssueState
    user: User
    labels: List[Label]
    assignees: List[User]
    milestone: Optional[Milestone] = None
    comments: int
    closed_at: Optional[str] = None


class Repository(BaseModel):
    id: int
    name: str
    full_name: str
    description: Optional[str] = None
    private: bool
    owner: User
    html_url: str
    clone_url: str
    default_branch: str
    language: Optional[str] = None
    stargazers_count: int
    forks_count: int
    open_issues_count: int
    topics: List[str]
    created_at: str
    updated_at: str
    pushed_at: Optional[str] = None


class GitRef(BaseModel):
    label: str
    ref: str = Field(alias="ref")
    sha: str
    user: User
    repo: Repository


class PullRequestState(str, Enum):
    open = "open"
    closed = "closed"


class PullRequest(BaseModel):
    id: int
    number: int
    title: str
    body: Optional[str] = None
    state: PullRequestState
    user: User
    head: GitRef
    base: GitRef
    merged: bool
    mergeable: Optional[bool] = None
    merged_by: Optional[User] = None
    comments: int
    commits: int
    additions: int
    deletions: int
    changed_files: int
    labels: List[Label]
    requested_reviewers: List[User]
