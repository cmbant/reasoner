import os
from agents import OpenAIChatCompletionsModel
from openai import AsyncOpenAI
from typing import Dict, Union


class ModelProvider:
    # API URL configurations
    API_URLS: Dict[str, str] = {
        'gemini': "https://generativelanguage.googleapis.com/v1beta/openai/",
        'anthropic': "https://api.anthropic.com/v1/",
        'openai': "https://api.openai.com/v1"
    }


def get_chat_model(model_string: str, api_key: str = None) -> Union[str, OpenAIChatCompletionsModel]:
    """
    Get model from string format 'api_type/model_name'
    Example: 'anthropic/claude-3-7-sonnet' or 'openai/gpt-4o'
    """
    if '/' not in model_string:
        return model_string
    try:
        api_type, model_name = model_string.split('/')
    except ValueError:
        raise ValueError("Model string must be in format 'api_type/model_name'")

    # For OpenAI models using key in env, just return the model name
    if not api_key and api_type == 'openai':
        return model_name

    # Get API key from environment
    env_var = f"{api_type.upper()}_API_KEY"
    api_key = api_key or os.getenv(env_var)
    if not api_key:
        raise ValueError(f"Environment variable {env_var} not set")

    # For other providers, create an external client
    external_client = AsyncOpenAI(
        api_key=api_key,
        base_url=ModelProvider.API_URLS.get(api_type)
    )

    return OpenAIChatCompletionsModel(
        model=model_name,
        openai_client=external_client,
    )
